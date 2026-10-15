import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8096000 in
set_option maxHeartbeats 8096000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8378 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h11313 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  rcases m.htr 0 2 5 (by decide) (by decide) with h11659 | h11659
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11660 | h11660
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11661 | h11661
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11662 | h11662
        · linarith only [h11659, h11662, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11664 | h11664
          · linarith only [h11313, h11659, h11664, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11666 | h11666
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11667 | h11667
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11668 | h11668
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11669 | h11669
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11670 | h11670
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11671 | h11671
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11672 | h11672
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11673 | h11673
                          · rcases h1bigk with h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h0, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h6794, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h7647, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h8170, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11664, h11670, hc01, hc23, hlam, hphi, ht12, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11662, hlam, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11664, hlam, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11664, h11670, h8170, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11674_1, u5ehi0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              rcases p11674_3 (m.d 0 1) (by simp) with h11685 | h11685
                              · linarith only [h11685, hlam, p11674_0]
                              · rcases p11674_3 (m.d 1 2) (by simp) with h11687 | h11687
                                · linarith only [h11662, h11687, hlam]
                                · linarith only [h0, h11687, hlam]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h0, h11659, h11662, h11664, h11671, h11673, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11674_1, u5ehi4]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11662, h8170, hc01, hc23, hlam, hphi, ht12, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              rcases p11674_3 (m.d 0 1) (by simp) with h11694 | h11694
                              · linarith only [h11694, hlam, p11674_0]
                              · rcases p11674_3 (m.d 1 2) (by simp) with h11696 | h11696
                                · linarith only [h11664, h11696, hlam]
                                · linarith only [h0, h11696, hlam]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h0, h11659, h11671, h11673, hc14, hlam, hphi, ht01, ht0b, ht5b, p11674_1, u5ehi4]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11667, hlam, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11664, h11670, h8170, hc01, hc23, hlam, hphi, ht12, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11662, h11666, hc01, hc23, hlam, hphi, ht12, p11674_1]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11666, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11668, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [h11669, hlam, p11674_0]
                            · have p11674_0 := h11674c.1
                              have p11674_1 := h11674c.2.1
                              have p11674_2 := h11674c.2.2.1
                              have p11674_3 := h11674c.2.2.2
                              linarith only [hlam, p11674_0]
                          · rcases h1bigk with h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c | h11708c
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h0, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h6794, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h7647, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h8170, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11664, h11670, hc01, hc23, hlam, hphi, ht12, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11662, hlam, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11664, hlam, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11664, h11670, h8170, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11708_1, u5ehi0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              rcases p11708_3 (m.d 0 1) (by simp) with h11719 | h11719
                              · linarith only [h11719, hlam, p11708_0]
                              · rcases p11708_3 (m.d 1 2) (by simp) with h11721 | h11721
                                · linarith only [h11662, h11721, hlam]
                                · linarith only [h0, h11721, hlam]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h0, h11659, h11662, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11708_1, u5ehi2]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11662, h7647, hc01, hc23, hlam, hphi, ht12, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11662, h8170, hc01, hc23, hlam, hphi, ht12, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              rcases p11708_3 (m.d 0 1) (by simp) with h11728 | h11728
                              · linarith only [h11728, hlam, p11708_0]
                              · rcases p11708_3 (m.d 1 2) (by simp) with h11730 | h11730
                                · linarith only [h11664, h11730, hlam]
                                · linarith only [h0, h11730, hlam]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h0, h11659, h11672, h11673, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11667, hlam, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11664, h11670, h8170, hc01, hc23, hlam, hphi, ht12, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11662, h11666, hc01, hc23, hlam, hphi, ht12, p11708_1]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11666, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11668, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [h11669, hlam, p11708_0]
                            · have p11708_0 := h11708c.1
                              have p11708_1 := h11708c.2.1
                              have p11708_2 := h11708c.2.2.1
                              have p11708_3 := h11708c.2.2.2
                              linarith only [hlam, p11708_0]
                        · linarith only [h0, h11664, h11672, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h11659, h11664, h11670, h11671, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h11659, h11670, h8378, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h11660, h11661, h11669, h6794, h7647, hc01, hc13, hlam, hphi]
                · linarith only [h11662, h11666, h11668, hlam]
              · linarith only [h0, h11659, h11660, h11662, h11667, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h11659, h11666, hlam]
      · linarith only [h11313, h11659, h11661, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11750 | h11750
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11751 | h11751
        · linarith only [h11659, h11751, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11753 | h11753
          · linarith only [h11313, h11659, h11751, h11753, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11755 | h11755
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11756 | h11756
              · linarith only [h11659, h11660, h11756, h8378, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11758 | h11758
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11759 | h11759
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11760 | h11760
                    · linarith only [h11756, h11758, h11760, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h11659, h11760, h8378, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h11659, h11750, h11751, h11756, h11759, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h11751, h11755, h11758, hlam]
            · linarith only [h0, h11659, h11755, hlam]
      · linarith only [h11313, h11659, h11750, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11767 | h11767
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11768 | h11768
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11769 | h11769
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11770 | h11770
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11771 | h11771
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11772 | h11772
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11773 | h11773
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11774 | h11774
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11775 | h11775
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11776 | h11776
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11777 | h11777
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11778 | h11778
                          · linarith only [h11767, h11769, h11778, h8378, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c | h11780c
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h0, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h6794, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h7647, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h8170, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              rcases p11780_3 (m.d 0 1) (by simp) with h11786 | h11786
                              · linarith only [h11786, hlam, p11780_0]
                              · rcases p11780_3 (m.d 1 2) (by simp) with h11788 | h11788
                                · rcases p11780_3 (m.d 1 3) (by simp) with h11789 | h11789
                                  · linarith only [h11769, h11789, hlam]
                                  · linarith only [h11789, h6794, hlam]
                                · linarith only [h11788, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h6794, hc01, hc12, hlam, hphi, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11768, h11778, h7647, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h0, h11659, h11771, hc01, hc12, hlam, hphi, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              rcases p11780_3 (m.d 0 1) (by simp) with h11797 | h11797
                              · linarith only [h11797, hlam, p11780_0]
                              · rcases p11780_3 (m.d 1 2) (by simp) with h11799 | h11799
                                · rcases p11780_3 (m.d 1 3) (by simp) with h11800 | h11800
                                  · rcases p11780_3 (m.d 1 4) (by simp) with h11801 | h11801
                                    · linarith only [h11772, h11801, hlam]
                                    · linarith only [h11801, h7647, hlam]
                                  · linarith only [h11800, hlam, p11780_0]
                                · linarith only [h0, h11799, hlam]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11769, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h7647, hc01, hc13, hlam, hphi, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h0, h11659, h11769, h11771, hc01, hc12, hlam, hphi, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              rcases p11780_3 (m.d 0 1) (by simp) with h11810 | h11810
                              · linarith only [h11810, hlam, p11780_0]
                              · rcases p11780_3 (m.d 1 2) (by simp) with h11812 | h11812
                                · rcases p11780_3 (m.d 1 3) (by simp) with h11813 | h11813
                                  · rcases p11780_3 (m.d 1 4) (by simp) with h11814 | h11814
                                    · rcases p11780_3 (m.d 1 5) (by simp) with h11815 | h11815
                                      · linarith only [h11774, h11815, hlam]
                                      · linarith only [h11815, h8170, hlam]
                                    · linarith only [h11814, hlam, p11780_0]
                                  · linarith only [h11813, h6794, hlam]
                                · linarith only [h0, h11812, hlam]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11770, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11772, hlam, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h0, h11659, h11771, hc01, hc14, hlam, hphi, p11780_1]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              rcases p11780_3 (m.d 0 1) (by simp) with h11825 | h11825
                              · linarith only [h11825, hlam, p11780_0]
                              · rcases p11780_3 (m.d 1 2) (by simp) with h11827 | h11827
                                · rcases p11780_3 (m.d 1 3) (by simp) with h11828 | h11828
                                  · rcases p11780_3 (m.d 1 4) (by simp) with h11829 | h11829
                                    · rcases p11780_3 (m.d 1 5) (by simp) with h11830 | h11830
                                      · rcases h2bigk with h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c | h11831c
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h8378, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11313, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11659, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          rcases p11831_3 (m.d 0 2) (by simp) with h11837 | h11837
                                          · linarith only [h0, h11837, hlam]
                                          · rcases p11831_3 (m.d 1 2) (by simp) with h11839 | h11839
                                            · rcases p11831_3 (m.d 2 3) (by simp) with h11840 | h11840
                                              · linarith only [h11769, h11840, hlam]
                                              · linarith only [h11840, h8378, hlam]
                                            · linarith only [h0, h11839, hlam]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h8378, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11313, h11768, h11778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11659, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11769, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11769, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11313, h11768, h11769, h11778, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11659, h11769, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11770, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11770, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11775, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11659, h11769, h11775, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h0, h11771, hc01, hc12, hlam, hphi, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11771, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11776, hlam, p11831_0]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [h11777, hlam, p11831_1]
                                        · have p11831_0 := h11831c.1
                                          have p11831_1 := h11831c.2.1
                                          have p11831_2 := h11831c.2.2.1
                                          have p11831_3 := h11831c.2.2.2
                                          linarith only [hlam, p11831_0]
                                      · linarith only [h11830, hlam, p11780_0]
                                    · linarith only [h11829, h7647, hlam]
                                  · linarith only [h11828, h6794, hlam]
                                · linarith only [h0, h11827, hlam]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11771, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11773, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [h11774, hlam, p11780_0]
                            · have p11780_0 := h11780c.1
                              have p11780_1 := h11780c.2.1
                              have p11780_2 := h11780c.2.2.1
                              have p11780_3 := h11780c.2.2.2
                              linarith only [hlam, p11780_0]
                        · linarith only [h0, h11313, h11767, h11768, h11769, h11777, h6794, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h11769, h11773, h11776, h8378, hc01, hc12, hlam, hphi]
                    · linarith only [h11767, h11775, h8378, hlam]
                  · linarith only [h11767, h11768, h11774, h7647, h8378, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11875 | h11875
                  · linarith only [h11772, h11773, h11875, hlam]
                  · linarith only [h11767, h11768, h11769, h11773, h11875, h7647, h8378, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h11767, h11769, h11772, h8378, hlam]
            · linarith only [h11767, h11768, h11769, h11771, h8378, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · linarith only [h11767, h11768, h11769, h11770, h8378, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11881 | h11881
          · linarith only [h11313, h11768, h11769, h11881, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11883 | h11883
            · linarith only [h0, h11659, h11769, h11883, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11885 | h11885
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11886 | h11886
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11887 | h11887
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11888 | h11888
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11889 | h11889
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11890 | h11890
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11891 | h11891
                          · rcases h1bigk with h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c | h11892c
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h6794, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h7647, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h8170, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11883, h11888, h11890, hc01, hc23, hlam, hphi, ht12, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11769, hlam, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11881, hlam, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11883, hlam, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              rcases p11892_3 (m.d 0 1) (by simp) with h11903 | h11903
                              · linarith only [h11903, hlam, p11892_0]
                              · rcases p11892_3 (m.d 1 2) (by simp) with h11905 | h11905
                                · linarith only [h11769, h11905, hlam]
                                · linarith only [h0, h11905, hlam]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11767, h11769, h11891, h7647, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11892_1, u5ehi4]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, h11769, h11883, hc01, hc23, hlam, hphi, ht12, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              rcases p11892_3 (m.d 0 1) (by simp) with h11912 | h11912
                              · linarith only [h11912, hlam, p11892_0]
                              · rcases p11892_3 (m.d 1 2) (by simp) with h11914 | h11914
                                · linarith only [h11881, h11914, hlam]
                                · linarith only [h0, h11914, hlam]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11885, hlam, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, h11881, h11883, h11888, hc01, hc23, hlam, hphi, ht12, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              rcases p11892_3 (m.d 0 1) (by simp) with h11921 | h11921
                              · linarith only [h11921, hlam, p11892_0]
                              · rcases p11892_3 (m.d 1 2) (by simp) with h11923 | h11923
                                · linarith only [h11883, h11923, hlam]
                                · linarith only [h0, h11923, hlam]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p11892_1]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11886, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [h11887, hlam, p11892_0]
                            · have p11892_0 := h11892c.1
                              have p11892_1 := h11892c.2.1
                              have p11892_2 := h11892c.2.2.1
                              have p11892_3 := h11892c.2.2.2
                              linarith only [hlam, p11892_0]
                          · rcases h1bigk with h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c | h11930c
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h0, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h6794, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h7647, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h8170, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11769, hc01, hc23, hlam, hphi, ht12, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11769, hlam, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11881, hlam, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11883, hlam, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              rcases p11930_3 (m.d 0 1) (by simp) with h11941 | h11941
                              · linarith only [h11941, hlam, p11930_0]
                              · rcases p11930_3 (m.d 1 2) (by simp) with h11943 | h11943
                                · linarith only [h11769, h11943, hlam]
                                · linarith only [h0, h11943, hlam]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h0, h11769, hc01, hc23, hlam, hphi, ht12, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11769, h7647, hc01, hc23, hlam, hphi, ht12, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11769, h8170, hc01, hc23, hlam, hphi, ht12, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              rcases p11930_3 (m.d 0 1) (by simp) with h11950 | h11950
                              · linarith only [h11950, hlam, p11930_0]
                              · rcases p11930_3 (m.d 1 2) (by simp) with h11952 | h11952
                                · linarith only [h11881, h11952, hlam]
                                · linarith only [h0, h11952, hlam]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11885, hlam, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h0, h11881, h11883, h11888, hc01, hc23, hlam, hphi, ht12, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              rcases p11930_3 (m.d 0 1) (by simp) with h11959 | h11959
                              · linarith only [h11959, hlam, p11930_0]
                              · rcases p11930_3 (m.d 1 2) (by simp) with h11961 | h11961
                                · linarith only [h11883, h11961, hlam]
                                · linarith only [h0, h11961, hlam]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p11930_1]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11886, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [h11887, hlam, p11930_0]
                            · have p11930_0 := h11930c.1
                              have p11930_1 := h11930c.2.1
                              have p11930_2 := h11930c.2.2.1
                              have p11930_3 := h11930c.2.2.2
                              linarith only [hlam, p11930_0]
                        · linarith only [h11767, h11768, h11769, h11881, h11890, h6794, h7647, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h11769, h11889, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11769, h11888, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11768, h11887, h7647, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11972 | h11972
                  · linarith only [h11885, h11886, h11972, hlam]
                  · linarith only [h11767, h11768, h11886, h11972, h6794, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h11767, h11885, h6794, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11976 | h11976
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11977 | h11977
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11978 | h11978
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11979 | h11979
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11980 | h11980
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11981 | h11981
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11982 | h11982
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11983 | h11983
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11984 | h11984
                        · linarith only [h0, h11313, h11768, h11976, h11982, h11984, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h11313, h11979, h11981, h11984, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h11976, h11980, h11983, h8378, hc01, hc12, hlam, hphi]
                    · linarith only [h11767, h11982, h8378, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11989 | h11989
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11990 | h11990
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11991 | h11991
                        · linarith only [h11981, h11991, h7647, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11993 | h11993
                          · linarith only [h0, h11313, h11767, h11977, h11981, h11993, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases h1bigk with h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c | h11995c
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h0, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h6794, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h7647, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h8170, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              rcases p11995_3 (m.d 0 1) (by simp) with h12001 | h12001
                              · linarith only [h12001, hlam, p11995_0]
                              · rcases p11995_3 (m.d 1 2) (by simp) with h12003 | h12003
                                · rcases p11995_3 (m.d 1 3) (by simp) with h12004 | h12004
                                  · linarith only [h11976, h12004, hlam]
                                  · linarith only [h12004, h6794, hlam]
                                · linarith only [h12003, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h6794, hc01, hc12, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h0, h11313, h11977, hc01, hc12, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h8170, hc01, hc12, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              rcases p11995_3 (m.d 0 1) (by simp) with h12012 | h12012
                              · linarith only [h12012, hlam, p11995_0]
                              · rcases p11995_3 (m.d 1 2) (by simp) with h12014 | h12014
                                · rcases p11995_3 (m.d 1 3) (by simp) with h12015 | h12015
                                  · rcases p11995_3 (m.d 1 4) (by simp) with h12016 | h12016
                                    · linarith only [h11979, h12016, hlam]
                                    · linarith only [h12016, h7647, hlam]
                                  · linarith only [h12015, hlam, p11995_0]
                                · linarith only [h0, h12014, hlam]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11976, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h0, h11313, h11977, hc01, hc13, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h0, h11313, h11976, h11978, h11991, hc01, hc12, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11981, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11977, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11979, hlam, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11981, hlam, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              rcases p11995_3 (m.d 0 1) (by simp) with h12030 | h12030
                              · linarith only [h12030, hlam, p11995_0]
                              · rcases p11995_3 (m.d 1 2) (by simp) with h12032 | h12032
                                · rcases p11995_3 (m.d 1 3) (by simp) with h12033 | h12033
                                  · rcases p11995_3 (m.d 1 4) (by simp) with h12034 | h12034
                                    · linarith only [h11981, h12034, hlam]
                                    · linarith only [h12034, h7647, hlam]
                                  · linarith only [h12033, h6794, hlam]
                                · linarith only [h0, h12032, hlam]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11978, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h11980, hlam, p11995_0]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [h7647, hc01, hc15, hlam, hphi, p11995_1]
                            · have p11995_0 := h11995c.1
                              have p11995_1 := h11995c.2.1
                              have p11995_2 := h11995c.2.2.1
                              have p11995_3 := h11995c.2.2.2
                              linarith only [hlam, p11995_0]
                      · linarith only [h0, h11976, h11980, h11990, h8378, hc01, hc12, hlam, hphi]
                    · linarith only [h11767, h11989, h8378, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12045 | h12045
                  · linarith only [h0, h11313, h11768, h11979, h11980, h12045, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12047 | h12047
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12048 | h12048
                      · linarith only [h11980, h12048, h6794, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12050 | h12050
                        · linarith only [h0, h11313, h11768, h11976, h12047, h12050, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12052 | h12052
                          · linarith only [h11767, h11980, h12045, h12052, h6794, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases h1bigk with h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c | h12054c
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h0, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h6794, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h7647, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h8170, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              rcases p12054_3 (m.d 0 1) (by simp) with h12060 | h12060
                              · linarith only [h12060, hlam, p12054_0]
                              · rcases p12054_3 (m.d 1 2) (by simp) with h12062 | h12062
                                · rcases p12054_3 (m.d 1 3) (by simp) with h12063 | h12063
                                  · linarith only [h11976, h12063, hlam]
                                  · linarith only [h12063, h6794, hlam]
                                · linarith only [h12062, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h6794, hc01, hc12, hlam, hphi, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h0, h11313, h11977, hc01, hc12, hlam, hphi, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h8170, hc01, hc12, hlam, hphi, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11980, h12052, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11976, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h0, h11313, h11977, hc01, hc13, hlam, hphi, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11980, hlam, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11979, h11980, h12052, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11977, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11979, hlam, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h12045, hlam, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              rcases p12054_3 (m.d 0 1) (by simp) with h12081 | h12081
                              · linarith only [h12081, hlam, p12054_0]
                              · rcases p12054_3 (m.d 1 2) (by simp) with h12083 | h12083
                                · rcases p12054_3 (m.d 1 3) (by simp) with h12084 | h12084
                                  · linarith only [h11980, h12084, hlam]
                                  · linarith only [h12084, h6794, hlam]
                                · linarith only [h0, h12083, hlam]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h11978, hlam, p12054_0]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h6794, hc01, hc15, hlam, hphi, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [h0, h11313, h11977, h11980, h12052, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12054_1]
                            · have p12054_0 := h12054c.1
                              have p12054_1 := h12054c.2.1
                              have p12054_2 := h12054c.2.2.1
                              have p12054_3 := h12054c.2.2.2
                              linarith only [hlam, p12054_0]
                    · linarith only [h11767, h12047, h8378, hlam]
              · linarith only [h11767, h11976, h11979, h8378, hlam]
            · linarith only [h0, h11976, h11978, h8378, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11976, h11977, h8378, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12096 | h12096
          · linarith only [h0, h11313, h11976, h12096, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12098 | h12098
            · linarith only [h0, h11659, h11976, h12098, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12100 | h12100
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12101 | h12101
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12102 | h12102
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12103 | h12103
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12104 | h12104
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12105 | h12105
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12106 | h12106
                          · linarith only [h0, h11313, h11767, h11768, h12106, h6794, hc01, hc13, hlam, hphi]
                          · rcases h1bigk with h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c | h12108c
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h6794, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h7647, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h8170, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12098, h12103, h12105, hc01, hc23, hlam, hphi, ht12, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h11976, hlam, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12096, hlam, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12098, hlam, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              rcases p12108_3 (m.d 0 1) (by simp) with h12119 | h12119
                              · linarith only [h12119, hlam, p12108_0]
                              · rcases p12108_3 (m.d 1 2) (by simp) with h12121 | h12121
                                · linarith only [h11976, h12121, hlam]
                                · linarith only [h0, h12121, hlam]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, h11976, hc01, hc23, hlam, hphi, ht12, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, h11313, h11768, h11976, h12102, hc01, hc23, hlam, hphi, ht12, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h11976, h8170, hc01, hc23, hlam, hphi, ht12, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              rcases p12108_3 (m.d 0 1) (by simp) with h12128 | h12128
                              · linarith only [h12128, hlam, p12108_0]
                              · rcases p12108_3 (m.d 1 2) (by simp) with h12130 | h12130
                                · linarith only [h12096, h12130, hlam]
                                · linarith only [h0, h12130, hlam]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12100, hlam, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, h11313, h11768, h12096, h12102, h12103, hc01, hc23, hlam, hphi, ht12, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              rcases p12108_3 (m.d 0 1) (by simp) with h12137 | h12137
                              · linarith only [h12137, hlam, p12108_0]
                              · rcases p12108_3 (m.d 1 2) (by simp) with h12139 | h12139
                                · linarith only [h12098, h12139, hlam]
                                · linarith only [h0, h12139, hlam]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p12108_1]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12101, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [h12102, hlam, p12108_0]
                            · have p12108_0 := h12108c.1
                              have p12108_1 := h12108c.2.1
                              have p12108_2 := h12108c.2.2.1
                              have p12108_3 := h12108c.2.2.2
                              linarith only [hlam, p12108_0]
                        · linarith only [h0, h12096, h12105, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h11976, h12104, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h11767, h11768, h11976, h12101, h12102, h12103, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12149 | h12149
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12150 | h12150
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12151 | h12151
                        · linarith only [h0, h12096, h12102, h12149, h12151, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h12096, h12151, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h12101, h12150, h8378, hc01, hc13, hlam, hphi]
                    · linarith only [h11767, h11976, h12101, h12102, h12149, h7647, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12156 | h12156
                  · linarith only [h0, h11313, h11768, h12100, h12101, h12156, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12158 | h12158
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12159 | h12159
                      · linarith only [h12101, h12159, h6794, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h11976, h12159, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11767, h11976, h12158, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h11767, h12100, h6794, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12164 | h12164
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12165 | h12165
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12166 | h12166
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12167 | h12167
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12168 | h12168
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12169 | h12169
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12170 | h12170
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12171 | h12171
                    · linarith only [h11767, h12164, h12165, h12171, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · linarith only [h0, h12165, h12168, h12171, h8378, hc01, hc12, hlam, hphi]
                  · linarith only [h12164, h12170, h7647, hlam]
                · linarith only [h11767, h12168, h12169, hc03, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12176 | h12176
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12177 | h12177
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12178 | h12178
                    · linarith only [h12168, h12176, h12178, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12180 | h12180
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12181 | h12181
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12182 | h12182
                          · rcases h1bigk with h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c | h12183c
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h0, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h6794, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h7647, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h8170, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              rcases p12183_3 (m.d 0 1) (by simp) with h12189 | h12189
                              · linarith only [h12189, hlam, p12183_0]
                              · rcases p12183_3 (m.d 1 2) (by simp) with h12191 | h12191
                                · rcases p12183_3 (m.d 1 3) (by simp) with h12192 | h12192
                                  · linarith only [h12165, h12192, hlam]
                                  · linarith only [h12192, h6794, hlam]
                                · linarith only [h12191, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12165, h12180, h12182, hc12, hlam, hphi, ht01, ht0b, ht5b, p12183_1, u5ehi4]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12165, h12168, h12180, h12182, hc12, hlam, hphi, ht01, ht0b, ht5b, p12183_1, u5ehi4]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h0, h11659, h12167, hc01, hc12, hlam, hphi, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12168, hc01, hc34, hlam, hphi, ht12, ht23, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12165, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12168, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h0, h11659, h12167, h12168, hc01, hc34, hlam, hphi, ht12, ht23, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              rcases p12183_3 (m.d 0 1) (by simp) with h12205 | h12205
                              · linarith only [h12205, hlam, p12183_0]
                              · rcases p12183_3 (m.d 1 2) (by simp) with h12207 | h12207
                                · rcases p12183_3 (m.d 1 3) (by simp) with h12208 | h12208
                                  · linarith only [h12168, h12208, hlam]
                                  · linarith only [h12208, h6794, hlam]
                                · linarith only [h0, h12207, hlam]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12166, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h6794, hc01, hc14, hlam, hphi, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h0, h11659, h12167, h12168, hc01, hc34, hlam, hphi, ht12, ht23, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12168, h12176, hc01, hc34, hlam, hphi, ht12, ht23, p12183_1]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12167, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12176, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [h12177, hlam, p12183_0]
                            · have p12183_0 := h12183c.1
                              have p12183_1 := h12183c.2.1
                              have p12183_2 := h12183c.2.2.1
                              have p12183_3 := h12183c.2.2.2
                              linarith only [hlam, p12183_0]
                          · linarith only [h12164, h12168, h12176, h12182, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · linarith only [h11313, h12164, h12181, hlam]
                      · linarith only [h0, h12168, h12176, h12180, h8378, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11313, h12164, h12166, h12177, h7647, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12225 | h12225
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12226 | h12226
                    · linarith only [h11767, h12164, h12165, h12226, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12228 | h12228
                      · linarith only [h12165, h12176, h12228, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12230 | h12230
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12231 | h12231
                          · rcases h1bigk with h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c | h12232c
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h0, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h6794, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h7647, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h8170, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              rcases p12232_3 (m.d 0 1) (by simp) with h12238 | h12238
                              · linarith only [h12238, hlam, p12232_0]
                              · rcases p12232_3 (m.d 1 2) (by simp) with h12240 | h12240
                                · rcases p12232_3 (m.d 1 3) (by simp) with h12241 | h12241
                                  · linarith only [h12165, h12241, hlam]
                                  · linarith only [h12241, h6794, hlam]
                                · linarith only [h12240, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h6794, hc01, hc12, hlam, hphi, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h7647, hc01, hc12, hlam, hphi, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h8170, hc01, hc12, hlam, hphi, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12176, h12231, hc01, hc34, hlam, hphi, ht12, ht23, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12165, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12168, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12176, hlam, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              rcases p12232_3 (m.d 0 1) (by simp) with h12254 | h12254
                              · linarith only [h12254, hlam, p12232_0]
                              · rcases p12232_3 (m.d 1 2) (by simp) with h12256 | h12256
                                · rcases p12232_3 (m.d 1 3) (by simp) with h12257 | h12257
                                  · linarith only [h12168, h12257, hlam]
                                  · linarith only [h12257, h6794, hlam]
                                · linarith only [h0, h12256, hlam]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12166, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h0, h12165, h8378, hc01, hc14, hlam, hphi, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h0, h12165, h12168, h12176, h8378, hc01, hc34, hlam, hphi, ht12, ht23, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              rcases p12232_3 (m.d 0 1) (by simp) with h12265 | h12265
                              · linarith only [h12265, hlam, p12232_0]
                              · rcases p12232_3 (m.d 1 2) (by simp) with h12267 | h12267
                                · rcases p12232_3 (m.d 1 3) (by simp) with h12268 | h12268
                                  · linarith only [h12176, h12268, hlam]
                                  · linarith only [h12268, h6794, hlam]
                                · linarith only [h0, h12267, hlam]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12167, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h0, h12165, h8378, hc01, hc15, hlam, hphi, p12232_1]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [h12225, hlam, p12232_0]
                            · have p12232_0 := h12232c.1
                              have p12232_1 := h12232c.2.1
                              have p12232_2 := h12232c.2.2.1
                              have p12232_3 := h12232c.2.2.2
                              linarith only [hlam, p12232_0]
                          · linarith only [h11313, h12164, h12168, h12231, h7647, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h11313, h12164, h12230, hlam]
                  · linarith only [h11313, h12164, h12166, h12225, h7647, hc01, hc12, hlam, hphi]
            · linarith only [h11313, h12164, h12166, h12167, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · linarith only [h0, h12165, h12166, h8378, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12281 | h12281
          · linarith only [h11313, h12164, h12165, h12281, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12283 | h12283
            · linarith only [h0, h11659, h12165, h12283, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12285 | h12285
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12286 | h12286
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12287 | h12287
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12288 | h12288
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12289 | h12289
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12290 | h12290
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12291 | h12291
                          · rcases h1bigk with h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c | h12292c
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h6794, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h7647, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h8170, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12283, h12288, h12290, hc01, hc23, hlam, hphi, ht12, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12165, hlam, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12281, hlam, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12283, hlam, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              rcases p12292_3 (m.d 0 1) (by simp) with h12303 | h12303
                              · linarith only [h12303, hlam, p12292_0]
                              · rcases p12292_3 (m.d 1 2) (by simp) with h12305 | h12305
                                · linarith only [h12165, h12305, hlam]
                                · linarith only [h0, h12305, hlam]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12164, h12165, h7647, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p12292_1, u5ehi4]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, h12165, h12283, hc01, hc23, hlam, hphi, ht12, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              rcases p12292_3 (m.d 0 1) (by simp) with h12312 | h12312
                              · linarith only [h12312, hlam, p12292_0]
                              · rcases p12292_3 (m.d 1 2) (by simp) with h12314 | h12314
                                · linarith only [h12281, h12314, hlam]
                                · linarith only [h0, h12314, hlam]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12285, hlam, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, h12165, h12283, h12285, hc01, hc23, hlam, hphi, ht12, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              rcases p12292_3 (m.d 0 1) (by simp) with h12321 | h12321
                              · linarith only [h12321, hlam, p12292_0]
                              · rcases p12292_3 (m.d 1 2) (by simp) with h12323 | h12323
                                · linarith only [h12283, h12323, hlam]
                                · linarith only [h0, h12323, hlam]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p12292_1]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12286, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [h12287, hlam, p12292_0]
                            · have p12292_0 := h12292c.1
                              have p12292_1 := h12292c.2.1
                              have p12292_2 := h12292c.2.2.1
                              have p12292_3 := h12292c.2.2.2
                              linarith only [hlam, p12292_0]
                          · linarith only [h0, h11767, h12164, h12165, h12285, h12291, h7647, h8378, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h11313, h11767, h12164, h12165, h12285, h12290, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h11767, h12164, h12165, h12285, h12289, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h12165, h12285, h12288, hlam]
                  · linarith only [h11767, h12164, h12285, h12287, h7647, hc01, hc13, hlam, hphi]
                · linarith only [h11767, h12285, h12286, h8378, hc02, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12336 | h12336
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12337 | h12337
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12338 | h12338
                    · linarith only [h12285, h12336, h12338, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h12165, h12338, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h12164, h12285, h12336, h12337, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12342 | h12342
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12343 | h12343
                    · linarith only [h0, h12165, h12285, h12343, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12165, h12343, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h12164, h12342, h7647, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12347 | h12347
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12348 | h12348
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12349 | h12349
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12350 | h12350
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12351 | h12351
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12352 | h12352
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12353 | h12353
                    · linarith only [h0, h11767, h12347, h12353, h8378, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12347, h12350, h12353, h8378, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12356 | h12356
                    · linarith only [h0, h11767, h12347, h12356, h8378, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h12347, h12350, h12356, h8378, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11767, h12350, h12351, h8378, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12360 | h12360
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12361 | h12361
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12362 | h12362
                    · linarith only [h12350, h12360, h12362, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12364 | h12364
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12365 | h12365
                        · linarith only [h0, h11767, h12164, h12348, h12365, h8378, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h11313, h12361, h12365, hc01, hc14, hlam, hphi]
                      · linarith only [h12350, h12360, h12364, hc23, hc34, hlam, hphi]
                  · linarith only [h12350, h12360, h12361, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12370 | h12370
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12371 | h12371
                    · linarith only [h0, h11767, h12347, h12371, h8378, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12373 | h12373
                      · linarith only [h12360, h12371, h12373, h6794, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12375 | h12375
                        · linarith only [h0, h11767, h12164, h12348, h12375, h8378, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h11313, h12370, h12375, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12378 | h12378
                    · linarith only [h0, h11767, h12347, h12350, h12370, h12378, h8378, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12380 | h12380
                      · linarith only [h12360, h12380, h6794, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12382 | h12382
                        · linarith only [h12370, h12382, h7647, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12384 | h12384
                          · linarith only [h0, h12347, h12350, h12370, h12384, h8378, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h12347, h12350, h12384, h8378, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h12347, h12349, h8378, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12347, h12348, h8378, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12389 | h12389
          · linarith only [h0, h11313, h12347, h12389, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12391 | h12391
            · linarith only [h0, h11659, h12347, h12391, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12393 | h12393
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12394 | h12394
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12395 | h12395
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12396 | h12396
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12397 | h12397
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12398 | h12398
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12399 | h12399
                          · linarith only [h0, h11767, h12164, h12393, h12399, h8378, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h11767, h12395, h12399, h8378, hc01, hc14, hlam, hphi]
                        · linarith only [h12389, h12395, h12398, hlam]
                      · linarith only [h0, h11767, h12164, h12389, h12395, h12396, h12397, h8378, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h11767, h12164, h12347, h12393, h12395, h12396, h8378, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12405 | h12405
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12406 | h12406
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12407 | h12407
                        · linarith only [h12395, h12407, h7647, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h12389, h12407, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h12347, h12394, h12406, hlam]
                    · linarith only [h0, h12347, h12405, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h11767, h12393, h12394, h8378, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12413 | h12413
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12414 | h12414
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12415 | h12415
                    · linarith only [h12393, h12413, h12415, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h12347, h12415, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h12393, h12413, h12414, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12419 | h12419
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12420 | h12420
                    · linarith only [h12393, h12420, h6794, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12347, h12420, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12423 | h12423
                    · linarith only [h0, h12347, h12393, h12423, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h12347, h12423, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 8096000 in
set_option maxHeartbeats 8096000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8378 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  rcases m.htr 0 2 4 (by decide) (by decide) with h11313 | h11313
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 h8378 h11313
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 h8378 h11313

set_option maxHeartbeats 8096000 in
set_option maxHeartbeats 8096000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8170 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  have h8170 := hg8170
  rcases m.htr 0 2 3 (by decide) (by decide) with h8378 | h8378
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x0 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 h8378
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10_x1 m hb1 hb2 hb4 hb5 hg0 hg6794 hg7647 hg8170 h8378

end R2N4
