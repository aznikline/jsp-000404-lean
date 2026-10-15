import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S11
import Jsp000404.R1LeavesN7_0S12
import Jsp000404.R1LeavesN7_0S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7434 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 2 3 4 (by decide) (by decide) with h8735 | h8735
  · rcases m.htr 2 3 5 (by decide) (by decide) with h8736 | h8736
    · rcases m.htr 2 4 5 (by decide) (by decide) with h8737 | h8737
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8738 | h8738
        · linarith only [h0, h4, h7434, h8735, h8738, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h10, h4, h4129, h8735, h8737, h8738, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8741 | h8741
        · linarith only [h0, h3576, h4, h7, h8737, h8741, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases h1bigk with h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c | h8743c
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h10, h4, h4129, h7, h8735, h8737, h9, hlam, p8743_2]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h4, h4129, h7, h8735, h8737, h9, hlam, p8743_2]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            rcases p8743_3 (m.d 0 1) (by simp) with h8747 | h8747
            · rcases p8743_3 (m.d 1 2) (by simp) with h8748 | h8748
              · linarith only [h0, h8748, hlam]
              · rcases p8743_3 (m.d 1 3) (by simp) with h8750 | h8750
                · linarith only [h1, h8750, hlam]
                · rcases p8743_3 (m.d 1 4) (by simp) with h8752 | h8752
                  · linarith only [h8752, hlam, p8743_0]
                  · rcases p8743_3 (m.d 1 5) (by simp) with h8754 | h8754
                    · linarith only [h3, h8754, hlam]
                    · linarith only [h7434, h8754, hlam]
            · linarith only [h8747, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            rcases p8743_3 (m.d 0 1) (by simp) with h8758 | h8758
            · rcases p8743_3 (m.d 1 2) (by simp) with h8759 | h8759
              · linarith only [h0, h8759, hlam]
              · rcases p8743_3 (m.d 1 3) (by simp) with h8761 | h8761
                · linarith only [h1, h8761, hlam]
                · rcases p8743_3 (m.d 1 4) (by simp) with h8763 | h8763
                  · linarith only [h2, h8763, hlam]
                  · rcases p8743_3 (m.d 1 5) (by simp) with h8765 | h8765
                    · linarith only [h8765, hlam, p8743_0]
                    · rcases h1emax with h8767 | h8767 | h8767 | h8767 | h8767
                      · linarith only [h0, h10, h4, h4129, h7, h8735, h8737, h8767, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c | h8769c
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h10, h4, h4129, h7, h8735, h8737, h9, hlam, p8769_2]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h0, h6948, h8736, hlam, p8743_2, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          rcases p8769_3 (m.d 0 2) (by simp) with h8773 | h8773
                          · rcases p8769_3 (m.d 1 2) (by simp) with h8774 | h8774
                            · linarith only [h0, h8774, hlam]
                            · rcases p8769_3 (m.d 2 3) (by simp) with h8776 | h8776
                              · linarith only [h4, h8776, hlam]
                              · linarith only [h8735, h8776, hlam]
                          · linarith only [h8773, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          rcases p8769_3 (m.d 0 2) (by simp) with h8780 | h8780
                          · rcases p8769_3 (m.d 1 2) (by simp) with h8781 | h8781
                            · linarith only [h0, h8781, hlam]
                            · rcases p8769_3 (m.d 2 3) (by simp) with h8783 | h8783
                              · linarith only [h4, h8783, hlam]
                              · linarith only [h8736, h8783, hlam]
                          · linarith only [h8780, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h0, hlam, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h10, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h3576, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h4058, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h4, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          rcases p8769_3 (m.d 0 2) (by simp) with h8793 | h8793
                          · rcases p8769_3 (m.d 1 2) (by simp) with h8794 | h8794
                            · linarith only [h8794, hlam, p8769_0]
                            · rcases p8769_3 (m.d 2 3) (by simp) with h8796 | h8796
                              · rcases p8769_3 (m.d 2 4) (by simp) with h8797 | h8797
                                · linarith only [h8735, h8797, hlam]
                                · linarith only [h3576, h8797, hlam]
                              · linarith only [h8796, hlam, p8769_0]
                          · linarith only [h0, h8793, hlam]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h10, h4129, h8735, hc12, hc23, hlam, hphi, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h0, h10, h4, h4129, h8735, h8737, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h5, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h7, h8737, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h8735, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h8737, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h6, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          rcases p8769_3 (m.d 0 2) (by simp) with h8811 | h8811
                          · rcases p8769_3 (m.d 1 2) (by simp) with h8812 | h8812
                            · linarith only [h8812, hlam, p8769_0]
                            · rcases p8769_3 (m.d 2 3) (by simp) with h8814 | h8814
                              · rcases p8769_3 (m.d 2 4) (by simp) with h8815 | h8815
                                · linarith only [h8737, h8815, hlam]
                                · linarith only [h3576, h8815, hlam]
                              · linarith only [h10, h8814, hlam]
                          · linarith only [h0, h8811, hlam]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h8736, hlam, p8769_0]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [h3576, hc12, hc25, hlam, hphi, p8769_1]
                        · have p8769_0 := h8769c.1
                          have p8769_1 := h8769c.2.1
                          have p8769_2 := h8769c.2.2.1
                          have p8769_3 := h8769c.2.2.2
                          linarith only [hlam, p8769_0]
                      · rcases h2bigk with h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c | h8823c
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h10, h4, h4129, h8735, hlam, p8823_2]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h0, h10, h4129, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          rcases p8823_3 (m.d 0 2) (by simp) with h8827 | h8827
                          · rcases p8823_3 (m.d 1 2) (by simp) with h8828 | h8828
                            · linarith only [h0, h8828, hlam]
                            · rcases p8823_3 (m.d 2 3) (by simp) with h8830 | h8830
                              · linarith only [h4, h8830, hlam]
                              · linarith only [h8735, h8830, hlam]
                          · linarith only [h8827, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          rcases p8823_3 (m.d 0 2) (by simp) with h8834 | h8834
                          · rcases p8823_3 (m.d 1 2) (by simp) with h8835 | h8835
                            · linarith only [h0, h8835, hlam]
                            · rcases p8823_3 (m.d 2 3) (by simp) with h8837 | h8837
                              · linarith only [h4, h8837, hlam]
                              · linarith only [h8736, h8837, hlam]
                          · linarith only [h8834, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h0, hlam, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h10, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h3576, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h4058, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h4, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          rcases p8823_3 (m.d 0 2) (by simp) with h8847 | h8847
                          · rcases p8823_3 (m.d 1 2) (by simp) with h8848 | h8848
                            · linarith only [h8848, hlam, p8823_0]
                            · rcases p8823_3 (m.d 2 3) (by simp) with h8850 | h8850
                              · rcases p8823_3 (m.d 2 4) (by simp) with h8851 | h8851
                                · linarith only [h8735, h8851, hlam]
                                · linarith only [h3576, h8851, hlam]
                              · linarith only [h8850, hlam, p8823_0]
                          · linarith only [h0, h8847, hlam]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h10, h4129, h8735, hc12, hc23, hlam, hphi, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h5, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h0, h4, h7, h8737, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h8735, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h8737, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h6, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          rcases p8823_3 (m.d 0 2) (by simp) with h8865 | h8865
                          · rcases p8823_3 (m.d 1 2) (by simp) with h8866 | h8866
                            · linarith only [h8866, hlam, p8823_0]
                            · rcases p8823_3 (m.d 2 3) (by simp) with h8868 | h8868
                              · rcases p8823_3 (m.d 2 4) (by simp) with h8869 | h8869
                                · linarith only [h8737, h8869, hlam]
                                · linarith only [h3576, h8869, hlam]
                              · linarith only [h10, h8868, hlam]
                          · linarith only [h0, h8865, hlam]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h8736, hlam, p8823_0]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [h3576, hc12, hc25, hlam, hphi, p8823_1]
                        · have p8823_0 := h8823c.1
                          have p8823_1 := h8823c.2.1
                          have p8823_2 := h8823c.2.2.1
                          have p8823_3 := h8823c.2.2.2
                          linarith only [hlam, p8823_0]
                      · rcases h2bigk with h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c | h8877c
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h10, h4, h4129, h8735, hlam, p8877_2]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h0, h10, h4129, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          rcases p8877_3 (m.d 0 2) (by simp) with h8881 | h8881
                          · rcases p8877_3 (m.d 1 2) (by simp) with h8882 | h8882
                            · linarith only [h0, h8882, hlam]
                            · rcases p8877_3 (m.d 2 3) (by simp) with h8884 | h8884
                              · linarith only [h4, h8884, hlam]
                              · linarith only [h8735, h8884, hlam]
                          · linarith only [h8881, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          rcases p8877_3 (m.d 0 2) (by simp) with h8888 | h8888
                          · rcases p8877_3 (m.d 1 2) (by simp) with h8889 | h8889
                            · linarith only [h0, h8889, hlam]
                            · rcases p8877_3 (m.d 2 3) (by simp) with h8891 | h8891
                              · linarith only [h4, h8891, hlam]
                              · linarith only [h8736, h8891, hlam]
                          · linarith only [h8888, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h0, hlam, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h10, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h3576, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h4058, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h4, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          rcases p8877_3 (m.d 0 2) (by simp) with h8901 | h8901
                          · rcases p8877_3 (m.d 1 2) (by simp) with h8902 | h8902
                            · linarith only [h8902, hlam, p8877_0]
                            · rcases p8877_3 (m.d 2 3) (by simp) with h8904 | h8904
                              · rcases p8877_3 (m.d 2 4) (by simp) with h8905 | h8905
                                · linarith only [h8735, h8905, hlam]
                                · linarith only [h3576, h8905, hlam]
                              · linarith only [h8904, hlam, p8877_0]
                          · linarith only [h0, h8901, hlam]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h10, h4129, h8735, hc12, hc23, hlam, hphi, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h5, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h0, h4, h7, h8737, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h8735, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h8737, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h6, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          rcases p8877_3 (m.d 0 2) (by simp) with h8919 | h8919
                          · rcases p8877_3 (m.d 1 2) (by simp) with h8920 | h8920
                            · linarith only [h8920, hlam, p8877_0]
                            · rcases p8877_3 (m.d 2 3) (by simp) with h8922 | h8922
                              · rcases p8877_3 (m.d 2 4) (by simp) with h8923 | h8923
                                · linarith only [h8737, h8923, hlam]
                                · linarith only [h3576, h8923, hlam]
                              · linarith only [h10, h8922, hlam]
                          · linarith only [h0, h8919, hlam]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h8736, hlam, p8877_0]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [h3576, hc12, hc25, hlam, hphi, p8877_1]
                        · have p8877_0 := h8877c.1
                          have p8877_1 := h8877c.2.1
                          have p8877_2 := h8877c.2.2.1
                          have p8877_3 := h8877c.2.2.2
                          linarith only [hlam, p8877_0]
                      · rcases h2bigk with h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c | h8931c
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h10, h4, h4129, h8735, hlam, p8931_2]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h0, h10, h4129, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          rcases p8931_3 (m.d 0 2) (by simp) with h8935 | h8935
                          · rcases p8931_3 (m.d 1 2) (by simp) with h8936 | h8936
                            · linarith only [h0, h8936, hlam]
                            · rcases p8931_3 (m.d 2 3) (by simp) with h8938 | h8938
                              · linarith only [h4, h8938, hlam]
                              · linarith only [h8735, h8938, hlam]
                          · linarith only [h8935, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          rcases p8931_3 (m.d 0 2) (by simp) with h8942 | h8942
                          · rcases p8931_3 (m.d 1 2) (by simp) with h8943 | h8943
                            · linarith only [h0, h8943, hlam]
                            · rcases p8931_3 (m.d 2 3) (by simp) with h8945 | h8945
                              · linarith only [h4, h8945, hlam]
                              · linarith only [h8736, h8945, hlam]
                          · linarith only [h8942, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h0, hlam, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h10, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h3576, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h4058, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h4, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          rcases p8931_3 (m.d 0 2) (by simp) with h8955 | h8955
                          · rcases p8931_3 (m.d 1 2) (by simp) with h8956 | h8956
                            · linarith only [h8956, hlam, p8931_0]
                            · rcases p8931_3 (m.d 2 3) (by simp) with h8958 | h8958
                              · rcases p8931_3 (m.d 2 4) (by simp) with h8959 | h8959
                                · linarith only [h8735, h8959, hlam]
                                · linarith only [h3576, h8959, hlam]
                              · linarith only [h8958, hlam, p8931_0]
                          · linarith only [h0, h8955, hlam]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h10, h4129, h8735, hc12, hc23, hlam, hphi, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h5, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h0, h4, h7, h8737, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h8735, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h8737, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h6, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          rcases p8931_3 (m.d 0 2) (by simp) with h8973 | h8973
                          · rcases p8931_3 (m.d 1 2) (by simp) with h8974 | h8974
                            · linarith only [h8974, hlam, p8931_0]
                            · rcases p8931_3 (m.d 2 3) (by simp) with h8976 | h8976
                              · rcases p8931_3 (m.d 2 4) (by simp) with h8977 | h8977
                                · linarith only [h8737, h8977, hlam]
                                · linarith only [h3576, h8977, hlam]
                              · linarith only [h10, h8976, hlam]
                          · linarith only [h0, h8973, hlam]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h8736, hlam, p8931_0]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [h3576, hc12, hc25, hlam, hphi, p8931_1]
                        · have p8931_0 := h8931c.1
                          have p8931_1 := h8931c.2.1
                          have p8931_2 := h8931c.2.2.1
                          have p8931_3 := h8931c.2.2.2
                          linarith only [hlam, p8931_0]
            · linarith only [h8758, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h10, hlam, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h3576, hlam, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h4058, hlam, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h1, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h4129, hc12, hc34, hlam, hphi, ht23, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h4129, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h6948, hlam, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h2, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h4, h7, h7434, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h10, h4, h7, h7434, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h7434, hlam, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h3, hlam, p8743_0]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h4, h6948, h8736, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h10, h4, h6948, h8736, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [h0, h4, h6948, h8736, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p8743_1]
          · have p8743_0 := h8743c.1
            have p8743_1 := h8743c.2.1
            have p8743_2 := h8743c.2.2.1
            have p8743_3 := h8743c.2.2.2
            linarith only [hlam, p8743_0]
    · linarith only [h10, h4129, h8735, h8736, hc12, hc35, hlam, hphi, ht23]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h9007 | h9007
    · linarith only [h10, h6948, h8735, h9007, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h9009 | h9009
      · rcases m.htr 3 4 5 (by decide) (by decide) with h9010 | h9010
        · rcases h1bigk with h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c | h9011c
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h10, h4, h7, h9007, h9010, hlam, p9011_2]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h4129, h7, h7434, h8735, h9009, hlam, p9011_2]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h7, h7434, h8735, h9009, hlam, p9011_2]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            rcases p9011_3 (m.d 0 1) (by simp) with h9016 | h9016
            · rcases p9011_3 (m.d 1 2) (by simp) with h9017 | h9017
              · linarith only [h0, h9017, hlam]
              · rcases p9011_3 (m.d 1 3) (by simp) with h9019 | h9019
                · linarith only [h1, h9019, hlam]
                · rcases p9011_3 (m.d 1 4) (by simp) with h9021 | h9021
                  · linarith only [h2, h9021, hlam]
                  · rcases p9011_3 (m.d 1 5) (by simp) with h9023 | h9023
                    · linarith only [h9023, hlam, p9011_0]
                    · rcases h1emax with h9025 | h9025 | h9025 | h9025 | h9025
                      · linarith only [h0, h10, h4, h4129, h7, h7434, h8735, h9009, h9025, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h2bigk with h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c | h9027c
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h10, h4, h4129, h7, h7434, h8735, h9009, hlam, p9027_2]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          rcases p9027_3 (m.d 0 2) (by simp) with h9030 | h9030
                          · rcases p9027_3 (m.d 1 2) (by simp) with h9031 | h9031
                            · linarith only [h0, h9031, hlam]
                            · rcases p9027_3 (m.d 2 3) (by simp) with h9033 | h9033
                              · linarith only [h9033, hlam, p9027_0]
                              · rcases p9027_3 (m.d 2 4) (by simp) with h9035 | h9035
                                · linarith only [h5, h9035, hlam]
                                · linarith only [h8735, h9035, hlam]
                          · linarith only [h9030, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h0, h10, h4129, h7434, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          rcases p9027_3 (m.d 0 2) (by simp) with h9040 | h9040
                          · rcases p9027_3 (m.d 1 2) (by simp) with h9041 | h9041
                            · linarith only [h0, h9041, hlam]
                            · rcases p9027_3 (m.d 2 3) (by simp) with h9043 | h9043
                              · linarith only [h4, h9043, hlam]
                              · rcases p9027_3 (m.d 2 4) (by simp) with h9045 | h9045
                                · linarith only [h5, h9045, hlam]
                                · linarith only [h9009, h9045, hlam]
                          · linarith only [h9040, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h0, hlam, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h10, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h3576, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h4058, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h4, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h7, h9007, h9010, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h8735, hlam, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h9007, hlam, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h5, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          rcases p9027_3 (m.d 0 2) (by simp) with h9060 | h9060
                          · rcases p9027_3 (m.d 1 2) (by simp) with h9061 | h9061
                            · linarith only [h9061, hlam, p9027_0]
                            · rcases p9027_3 (m.d 2 3) (by simp) with h9063 | h9063
                              · linarith only [h8735, h9063, hlam]
                              · linarith only [h10, h9063, hlam]
                          · linarith only [h0, h9060, hlam]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h10, hc12, hc24, hlam, hphi, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h0, h4, h4058, h7, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h6, hlam, p9027_0]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          rcases p9027_3 (m.d 0 2) (by simp) with h9071 | h9071
                          · rcases p9027_3 (m.d 1 2) (by simp) with h9072 | h9072
                            · linarith only [h9072, hlam, p9027_0]
                            · rcases p9027_3 (m.d 2 3) (by simp) with h9074 | h9074
                              · linarith only [h9007, h9074, hlam]
                              · linarith only [h10, h9074, hlam]
                          · linarith only [h0, h9071, hlam]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h10, hc12, hc25, hlam, hphi, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [h9009, hlam, p9027_1]
                        · have p9027_0 := h9027c.1
                          have p9027_1 := h9027c.2.1
                          have p9027_2 := h9027c.2.2.1
                          have p9027_3 := h9027c.2.2.2
                          linarith only [hlam, p9027_0]
                      · rcases h2bigk with h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c | h9081c
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h10, h4, h7, h8735, hlam, p9081_2]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          rcases p9081_3 (m.d 0 2) (by simp) with h9084 | h9084
                          · rcases p9081_3 (m.d 1 2) (by simp) with h9085 | h9085
                            · linarith only [h0, h9085, hlam]
                            · rcases p9081_3 (m.d 2 3) (by simp) with h9087 | h9087
                              · linarith only [h9087, hlam, p9081_0]
                              · rcases p9081_3 (m.d 2 4) (by simp) with h9089 | h9089
                                · linarith only [h5, h9089, hlam]
                                · linarith only [h8735, h9089, hlam]
                          · linarith only [h9084, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h0, h10, h4129, h7434, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          rcases p9081_3 (m.d 0 2) (by simp) with h9094 | h9094
                          · rcases p9081_3 (m.d 1 2) (by simp) with h9095 | h9095
                            · linarith only [h0, h9095, hlam]
                            · rcases p9081_3 (m.d 2 3) (by simp) with h9097 | h9097
                              · linarith only [h4, h9097, hlam]
                              · rcases p9081_3 (m.d 2 4) (by simp) with h9099 | h9099
                                · linarith only [h5, h9099, hlam]
                                · linarith only [h9009, h9099, hlam]
                          · linarith only [h9094, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h0, hlam, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h10, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h3576, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h4058, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h4, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h0, h4, h7, h9007, h9010, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h8735, hlam, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h9007, hlam, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h5, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          rcases p9081_3 (m.d 0 2) (by simp) with h9114 | h9114
                          · rcases p9081_3 (m.d 1 2) (by simp) with h9115 | h9115
                            · linarith only [h9115, hlam, p9081_0]
                            · rcases p9081_3 (m.d 2 3) (by simp) with h9117 | h9117
                              · linarith only [h8735, h9117, hlam]
                              · linarith only [h10, h9117, hlam]
                          · linarith only [h0, h9114, hlam]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h0, h4, h4058, h7, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h6, hlam, p9081_0]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          rcases p9081_3 (m.d 0 2) (by simp) with h9125 | h9125
                          · rcases p9081_3 (m.d 1 2) (by simp) with h9126 | h9126
                            · linarith only [h9126, hlam, p9081_0]
                            · rcases p9081_3 (m.d 2 3) (by simp) with h9128 | h9128
                              · linarith only [h9007, h9128, hlam]
                              · linarith only [h10, h9128, hlam]
                          · linarith only [h0, h9125, hlam]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h10, hc12, hc25, hlam, hphi, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [h9009, hlam, p9081_1]
                        · have p9081_0 := h9081c.1
                          have p9081_1 := h9081c.2.1
                          have p9081_2 := h9081c.2.2.1
                          have p9081_3 := h9081c.2.2.2
                          linarith only [hlam, p9081_0]
                      · rcases h2bigk with h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c | h9135c
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h10, h4, h7, h8735, hlam, p9135_2]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          rcases p9135_3 (m.d 0 2) (by simp) with h9138 | h9138
                          · rcases p9135_3 (m.d 1 2) (by simp) with h9139 | h9139
                            · linarith only [h0, h9139, hlam]
                            · rcases p9135_3 (m.d 2 3) (by simp) with h9141 | h9141
                              · linarith only [h9141, hlam, p9135_0]
                              · rcases p9135_3 (m.d 2 4) (by simp) with h9143 | h9143
                                · linarith only [h5, h9143, hlam]
                                · linarith only [h8735, h9143, hlam]
                          · linarith only [h9138, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h0, h10, h4129, h7434, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          rcases p9135_3 (m.d 0 2) (by simp) with h9148 | h9148
                          · rcases p9135_3 (m.d 1 2) (by simp) with h9149 | h9149
                            · linarith only [h0, h9149, hlam]
                            · rcases p9135_3 (m.d 2 3) (by simp) with h9151 | h9151
                              · linarith only [h4, h9151, hlam]
                              · rcases p9135_3 (m.d 2 4) (by simp) with h9153 | h9153
                                · linarith only [h5, h9153, hlam]
                                · linarith only [h9009, h9153, hlam]
                          · linarith only [h9148, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h0, hlam, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h10, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h3576, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h4058, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h4, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h0, h4, h7, h9007, h9010, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h8735, hlam, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h9007, hlam, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h5, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          rcases p9135_3 (m.d 0 2) (by simp) with h9168 | h9168
                          · rcases p9135_3 (m.d 1 2) (by simp) with h9169 | h9169
                            · linarith only [h9169, hlam, p9135_0]
                            · rcases p9135_3 (m.d 2 3) (by simp) with h9171 | h9171
                              · linarith only [h8735, h9171, hlam]
                              · linarith only [h10, h9171, hlam]
                          · linarith only [h0, h9168, hlam]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h0, h4, h4058, h7, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h6, hlam, p9135_0]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          rcases p9135_3 (m.d 0 2) (by simp) with h9179 | h9179
                          · rcases p9135_3 (m.d 1 2) (by simp) with h9180 | h9180
                            · linarith only [h9180, hlam, p9135_0]
                            · rcases p9135_3 (m.d 2 3) (by simp) with h9182 | h9182
                              · linarith only [h9007, h9182, hlam]
                              · linarith only [h10, h9182, hlam]
                          · linarith only [h0, h9179, hlam]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h10, hc12, hc25, hlam, hphi, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [h9009, hlam, p9135_1]
                        · have p9135_0 := h9135c.1
                          have p9135_1 := h9135c.2.1
                          have p9135_2 := h9135c.2.2.1
                          have p9135_3 := h9135c.2.2.2
                          linarith only [hlam, p9135_0]
                      · rcases h2bigk with h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c | h9189c
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h10, h4, h7, h8735, hlam, p9189_2]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          rcases p9189_3 (m.d 0 2) (by simp) with h9192 | h9192
                          · rcases p9189_3 (m.d 1 2) (by simp) with h9193 | h9193
                            · linarith only [h0, h9193, hlam]
                            · rcases p9189_3 (m.d 2 3) (by simp) with h9195 | h9195
                              · linarith only [h9195, hlam, p9189_0]
                              · rcases p9189_3 (m.d 2 4) (by simp) with h9197 | h9197
                                · linarith only [h5, h9197, hlam]
                                · linarith only [h8735, h9197, hlam]
                          · linarith only [h9192, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h0, h10, h4129, h7434, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          rcases p9189_3 (m.d 0 2) (by simp) with h9202 | h9202
                          · rcases p9189_3 (m.d 1 2) (by simp) with h9203 | h9203
                            · linarith only [h0, h9203, hlam]
                            · rcases p9189_3 (m.d 2 3) (by simp) with h9205 | h9205
                              · linarith only [h4, h9205, hlam]
                              · rcases p9189_3 (m.d 2 4) (by simp) with h9207 | h9207
                                · linarith only [h5, h9207, hlam]
                                · linarith only [h9009, h9207, hlam]
                          · linarith only [h9202, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h0, hlam, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h10, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h3576, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h4058, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h4, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h0, h4, h7, h9007, h9010, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h8735, hlam, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h9007, hlam, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h5, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          rcases p9189_3 (m.d 0 2) (by simp) with h9222 | h9222
                          · rcases p9189_3 (m.d 1 2) (by simp) with h9223 | h9223
                            · linarith only [h9223, hlam, p9189_0]
                            · rcases p9189_3 (m.d 2 3) (by simp) with h9225 | h9225
                              · linarith only [h8735, h9225, hlam]
                              · linarith only [h10, h9225, hlam]
                          · linarith only [h0, h9222, hlam]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h10, hc12, hc24, hlam, hphi, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h0, h4, h4058, h7, h8735, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h6, hlam, p9189_0]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          rcases p9189_3 (m.d 0 2) (by simp) with h9233 | h9233
                          · rcases p9189_3 (m.d 1 2) (by simp) with h9234 | h9234
                            · linarith only [h9234, hlam, p9189_0]
                            · rcases p9189_3 (m.d 2 3) (by simp) with h9236 | h9236
                              · linarith only [h9007, h9236, hlam]
                              · linarith only [h10, h9236, hlam]
                          · linarith only [h0, h9233, hlam]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h10, hc12, hc25, hlam, hphi, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [h9009, hlam, p9189_1]
                        · have p9189_0 := h9189c.1
                          have p9189_1 := h9189c.2.1
                          have p9189_2 := h9189c.2.2.1
                          have p9189_3 := h9189c.2.2.2
                          linarith only [hlam, p9189_0]
            · linarith only [h9016, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h10, hlam, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h3576, hlam, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h4058, hlam, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h1, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h4129, h7434, hc12, hc45, hlam, hphi, ht23, ht34, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h4129, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h6948, hlam, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h2, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h7, h7434, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h7, h7434, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h7434, hlam, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h3, hlam, p9011_0]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h7, h7434, h8735, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h10, h4, h7, h7434, h8735, h9009, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [h0, h4, h7, h7434, h8735, h9009, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p9011_1]
          · have p9011_0 := h9011c.1
            have p9011_1 := h9011c.2.1
            have p9011_2 := h9011c.2.2.1
            have p9011_3 := h9011c.2.2.2
            linarith only [hlam, p9011_0]
        · linarith only [h8735, h9009, h9010, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h9265 | h9265
        · linarith only [h0, h10, h4, h7, h8735, h9009, h9265, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h10, h8735, h9265, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 1 4 5 (by decide) (by decide) with h7434 | h7434
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948 h7434
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948 h7434

set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 1 3 5 (by decide) (by decide) with h6948 | h6948
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948

set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 1 3 4 (by decide) (by decide) with h4129 | h4129
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129

set_option maxHeartbeats 10420000 in
set_option maxHeartbeats 10420000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  have h10 := hg10
  have h3576 := hg3576
  rcases m.htr 1 2 5 (by decide) (by decide) with h4058 | h4058
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4059 | h4059
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4060 | h4060
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4061 | h4061
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4062 | h4062
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4063 | h4063
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4064 | h4064
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4065 | h4065
                · rcases h1bigk with h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    rcases p4066_3 (m.d 0 1) (by simp) with h4068 | h4068
                    · rcases p4066_3 (m.d 1 2) (by simp) with h4069 | h4069
                      · linarith only [h4069, hlam, p4066_0]
                      · rcases p4066_3 (m.d 1 3) (by simp) with h4071 | h4071
                        · linarith only [h1, h4071, hlam]
                        · linarith only [h10, h4071, hlam]
                    · linarith only [h4068, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h4059, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    rcases p4066_3 (m.d 0 1) (by simp) with h4076 | h4076
                    · rcases p4066_3 (m.d 1 2) (by simp) with h4077 | h4077
                      · linarith only [h0, h4077, hlam]
                      · rcases p4066_3 (m.d 1 3) (by simp) with h4079 | h4079
                        · linarith only [h1, h4079, hlam]
                        · linarith only [h4059, h4079, hlam]
                    · linarith only [h4076, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    rcases p4066_3 (m.d 0 1) (by simp) with h4083 | h4083
                    · rcases p4066_3 (m.d 1 2) (by simp) with h4084 | h4084
                      · linarith only [h0, h4084, hlam]
                      · linarith only [h4058, h4084, hlam]
                    · linarith only [h4083, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h0, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h10, hlam, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h3576, hlam, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h0, h3576, h4, h4062, hc01, hc15, hlam, hphi, ht0b, ht5b, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h1, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h0, h10, h4, h4058, h4063, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h0, h10, h3576, h4, h4058, h4063, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    rcases p4066_3 (m.d 0 1) (by simp) with h4097 | h4097
                    · rcases p4066_3 (m.d 1 2) (by simp) with h4098 | h4098
                      · linarith only [h10, h4098, hlam]
                      · linarith only [h4058, h4098, hlam]
                    · linarith only [h3, h4097, hlam]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h2, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h2, h4058, h4063, h4065, hc01, hc45, hlam, hphi, ht0b, ht5b, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h4059, hlam, p4066_1]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    rcases p4066_3 (m.d 0 1) (by simp) with h4106 | h4106
                    · rcases p4066_3 (m.d 1 2) (by simp) with h4107 | h4107
                      · linarith only [h3576, h4107, hlam]
                      · linarith only [h4058, h4107, hlam]
                    · linarith only [h3, h4106, hlam]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h3, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h4058, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h4060, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [h4061, hlam, p4066_0]
                  · have p4066_0 := h4066c.1
                    have p4066_1 := h4066c.2.1
                    have p4066_2 := h4066c.2.2.1
                    have p4066_3 := h4066c.2.2.2
                    linarith only [hlam, p4066_0]
                · linarith only [h0, h10, h4, h4058, h4064, h4065, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h3, h3576, h4058, h4061, h4064, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h3576, h4, h4058, h4062, h4063, h8, hc02, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h4058, h4062, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h3576, h4058, h4061, hlam]
      · linarith only [h10, h4058, h4060, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4122 | h4122
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4123 | h4123
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4124 | h4124
          · linarith only [h0, h4, h4059, h4122, h4124, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h4, h4058, h4124, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h10, h4058, h4059, h4123, hlam]
      · linarith only [h10, h4058, h4122, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h3576 h4058

end R2N4
