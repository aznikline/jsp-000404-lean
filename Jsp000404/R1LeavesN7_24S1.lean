import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h369 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
  · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
    · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
      · rcases m.htr 1 3 5 (by decide) (by decide) with h788 | h788
        · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
          · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
            · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
              · linarith only [h369, h785, h791, h9, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h793 | h793
                · linarith only [h369, h4, h786, h789, h791, h793, h9, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · rcases h0bigk with h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c | h795c
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h369, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h369, h4, h786, h789, h791, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h799 | h799
                    · rcases p795_3 (m.d 0 2) (by simp) with h800 | h800
                      · linarith only [h0, h800, hlam]
                      · linarith only [h5, h800, hlam]
                    · linarith only [h2, h799, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h804 | h804
                    · rcases p795_3 (m.d 0 2) (by simp) with h805 | h805
                      · linarith only [h0, h805, hlam]
                      · linarith only [h6, h805, hlam]
                    · linarith only [h3, h804, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h0, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h0, h369, h4, h786, h789, h791, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h812 | h812
                    · rcases p795_3 (m.d 0 2) (by simp) with h813 | h813
                      · rcases p795_3 (m.d 0 3) (by simp) with h814 | h814
                        · linarith only [h4, h814, hlam]
                        · linarith only [h7, h814, hlam]
                      · linarith only [h5, h813, hlam]
                    · linarith only [h2, h812, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h819 | h819
                    · rcases p795_3 (m.d 0 2) (by simp) with h820 | h820
                      · rcases p795_3 (m.d 0 3) (by simp) with h821 | h821
                        · linarith only [h4, h821, hlam]
                        · linarith only [h8, h821, hlam]
                      · linarith only [h6, h820, hlam]
                    · linarith only [h3, h819, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h1, hlam, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h4, hlam, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h829 | h829
                    · rcases p795_3 (m.d 0 2) (by simp) with h830 | h830
                      · rcases p795_3 (m.d 0 3) (by simp) with h831 | h831
                        · rcases p795_3 (m.d 0 4) (by simp) with h832 | h832
                          · linarith only [h7, h832, hlam]
                          · rcases p795_3 (m.d 0 5) (by simp) with h834 | h834
                            · linarith only [h8, h834, hlam]
                            · linarith only [h834, h9, hlam]
                        · linarith only [h7, h831, hlam]
                      · linarith only [h5, h830, hlam]
                    · linarith only [h2, h829, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h840 | h840
                    · rcases p795_3 (m.d 0 2) (by simp) with h841 | h841
                      · rcases p795_3 (m.d 0 3) (by simp) with h842 | h842
                        · rcases p795_3 (m.d 0 4) (by simp) with h843 | h843
                          · linarith only [h7, h843, hlam]
                          · rcases p795_3 (m.d 0 5) (by simp) with h845 | h845
                            · linarith only [h8, h845, hlam]
                            · rcases h0emin with h847 | h847 | h847 | h847 | h847
                              · rcases h2bigk with h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c | h848c
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  rcases p848_3 (m.d 0 2) (by simp) with h850 | h850
                                  · rcases p848_3 (m.d 1 2) (by simp) with h851 | h851
                                    · linarith only [h0, h851, hlam]
                                    · rcases p848_3 (m.d 2 3) (by simp) with h853 | h853
                                      · linarith only [h4, h853, hlam]
                                      · linarith only [h369, h853, hlam]
                                  · linarith only [h0, h850, hlam]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h0, h369, h786, h789, h791, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p848_1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, h4, h786, h791, hlam, p848_2]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, h4, h786, hlam, p848_2]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h0, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, h4, h789, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p848_1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, h4, h789, h791, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p848_1, u3elo0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h4, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h4, hc12, hlam, hphi, ht23, p848_1, u3elo0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  rcases p848_3 (m.d 0 2) (by simp) with h868 | h868
                                  · rcases p848_3 (m.d 1 2) (by simp) with h869 | h869
                                    · linarith only [h369, h869, hlam]
                                    · linarith only [h785, h869, hlam]
                                  · linarith only [h5, h868, hlam]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  rcases p848_3 (m.d 0 2) (by simp) with h873 | h873
                                  · rcases p848_3 (m.d 1 2) (by simp) with h874 | h874
                                    · linarith only [h369, h874, hlam]
                                    · linarith only [h786, h874, hlam]
                                  · linarith only [h6, h873, hlam]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h5, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h785, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h789, hlam, p848_1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h791, hlam, p848_1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h6, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h786, hlam, p848_0]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h790, hlam, p848_1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [h369, h786, h789, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p848_1, u3elo1]
                                · have p848_0 := h848c.1
                                  have p848_1 := h848c.2.1
                                  have p848_2 := h848c.2.2.1
                                  have p848_3 := h848c.2.2.2
                                  linarith only [hlam, p848_0]
                              · rcases h2bigk with h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c | h888c
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  rcases p888_3 (m.d 0 2) (by simp) with h890 | h890
                                  · rcases p888_3 (m.d 1 2) (by simp) with h891 | h891
                                    · linarith only [h0, h891, hlam]
                                    · rcases p888_3 (m.d 2 3) (by simp) with h893 | h893
                                      · linarith only [h4, h893, hlam]
                                      · linarith only [h369, h893, hlam]
                                  · linarith only [h0, h890, hlam]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h0, h369, h785, h789, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h369, h4, h785, hlam, p888_2]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h369, h4, h786, hlam, p888_2]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h0, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h369, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h369, h4, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h369, h4, hc02, hc25, hlam, hphi, ht0b, ht5b, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h4, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p888_1, u3elo2]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  rcases p888_3 (m.d 0 2) (by simp) with h908 | h908
                                  · rcases p888_3 (m.d 1 2) (by simp) with h909 | h909
                                    · linarith only [h369, h909, hlam]
                                    · linarith only [h785, h909, hlam]
                                  · linarith only [h5, h908, hlam]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  rcases p888_3 (m.d 0 2) (by simp) with h913 | h913
                                  · rcases p888_3 (m.d 1 2) (by simp) with h914 | h914
                                    · linarith only [h369, h914, hlam]
                                    · linarith only [h786, h914, hlam]
                                  · linarith only [h6, h913, hlam]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h5, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h785, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h789, hlam, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h791, hlam, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h6, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h786, hlam, p888_0]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h790, hlam, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [h0, h786, h789, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p888_1]
                                · have p888_0 := h888c.1
                                  have p888_1 := h888c.2.1
                                  have p888_2 := h888c.2.2.1
                                  have p888_3 := h888c.2.2.2
                                  linarith only [hlam, p888_0]
                              · linarith only [h847, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h847, h9, hlam, ht01, ht12, ht23, p795_1, u3elo0]
                              · linarith only [h847, hlam, ht01, ht12, ht23, p795_1, u3elo0]
                        · linarith only [h8, h842, hlam]
                      · linarith only [h6, h841, hlam]
                    · linarith only [h3, h840, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h2, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h5, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h7, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h9, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h3, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h6, hlam, p795_1]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [h8, hlam, p795_0]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    rcases p795_3 (m.d 0 1) (by simp) with h942 | h942
                    · rcases p795_3 (m.d 0 2) (by simp) with h943 | h943
                      · rcases p795_3 (m.d 0 3) (by simp) with h944 | h944
                        · rcases p795_3 (m.d 0 4) (by simp) with h945 | h945
                          · linarith only [h9, h945, hlam]
                          · rcases p795_3 (m.d 0 5) (by simp) with h947 | h947
                            · rcases h0emin with h948 | h948 | h948 | h948 | h948
                              · rcases h2bigk with h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c | h949c
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  rcases p949_3 (m.d 0 2) (by simp) with h951 | h951
                                  · rcases p949_3 (m.d 1 2) (by simp) with h952 | h952
                                    · linarith only [h0, h952, hlam]
                                    · rcases p949_3 (m.d 2 3) (by simp) with h954 | h954
                                      · linarith only [h4, h954, hlam]
                                      · linarith only [h369, h954, hlam]
                                  · linarith only [h0, h951, hlam]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h0, h369, h786, hc01, hc25, hlam, hphi, ht0b, ht5b, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h369, h4, h785, hlam, p949_2]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h369, h4, h786, hlam, p949_2]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h0, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h369, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h369, h4, h789, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h369, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p949_1, u3elo0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h4, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h4, hc12, hlam, hphi, ht23, p949_1, u3elo0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  rcases p949_3 (m.d 0 2) (by simp) with h969 | h969
                                  · rcases p949_3 (m.d 1 2) (by simp) with h970 | h970
                                    · linarith only [h369, h970, hlam]
                                    · linarith only [h785, h970, hlam]
                                  · linarith only [h5, h969, hlam]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  rcases p949_3 (m.d 0 2) (by simp) with h974 | h974
                                  · rcases p949_3 (m.d 1 2) (by simp) with h975 | h975
                                    · linarith only [h369, h975, hlam]
                                    · linarith only [h786, h975, hlam]
                                  · linarith only [h6, h974, hlam]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h5, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h785, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h789, hlam, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h791, hlam, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h6, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h786, hlam, p949_0]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h790, hlam, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [h0, h786, h789, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p949_1]
                                · have p949_0 := h949c.1
                                  have p949_1 := h949c.2.1
                                  have p949_2 := h949c.2.2.1
                                  have p949_3 := h949c.2.2.2
                                  linarith only [hlam, p949_0]
                              · rcases h2bigk with h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c | h989c
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  rcases p989_3 (m.d 0 2) (by simp) with h991 | h991
                                  · rcases p989_3 (m.d 1 2) (by simp) with h992 | h992
                                    · linarith only [h0, h992, hlam]
                                    · rcases p989_3 (m.d 2 3) (by simp) with h994 | h994
                                      · linarith only [h4, h994, hlam]
                                      · linarith only [h369, h994, hlam]
                                  · linarith only [h0, h991, hlam]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, h369, h786, hc01, hc25, hlam, hphi, ht0b, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h369, h4, h785, hlam, p989_2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h369, h4, h786, hlam, p989_2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h369, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h369, h4, h789, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h369, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p989_1, u3elo0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h4, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h4, hc12, hlam, hphi, ht23, p989_1, u3elo0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  rcases p989_3 (m.d 0 2) (by simp) with h1009 | h1009
                                  · rcases p989_3 (m.d 1 2) (by simp) with h1010 | h1010
                                    · linarith only [h1010, h369, hlam]
                                    · linarith only [h1010, h785, hlam]
                                  · linarith only [h1009, h5, hlam]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  rcases p989_3 (m.d 0 2) (by simp) with h1014 | h1014
                                  · rcases p989_3 (m.d 1 2) (by simp) with h1015 | h1015
                                    · linarith only [h1015, h369, hlam]
                                    · linarith only [h1015, h786, hlam]
                                  · linarith only [h1014, h6, hlam]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h5, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h785, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h789, hlam, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h791, hlam, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h6, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h786, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h790, hlam, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, h786, h789, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                              · linarith only [h948, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h948, hc05, hlam, p795_1]
                              · linarith only [h8, h948, hlam, ht01, ht12, ht23, u3elo0]
                            · linarith only [h9, h947, hlam]
                        · linarith only [h7, h944, hlam]
                      · linarith only [h5, h943, hlam]
                    · linarith only [h2, h942, hlam]
                  · have p795_0 := h795c.1
                    have p795_1 := h795c.2.1
                    have p795_2 := h795c.2.2.1
                    have p795_3 := h795c.2.2.2
                    linarith only [hlam, p795_0]
            · linarith only [h369, h790, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h369, h785, h789, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
        · linarith only [h788, h8, hc13, hlam, hphi, u3elo0]
      · linarith only [h369, h7, h785, h787, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1042 | h1042
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1043 | h1043
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1044 | h1044
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1045 | h1045
              · linarith only [h1044, h1045, h785, h786, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1047 | h1047
                · linarith only [h1043, h1044, h1047, h4, h785, h786, h9, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · rcases h0bigk with h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1043, h1044, h4, h785, h786, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1043, h1044, h4, h785, h786, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    rcases p1049_3 (m.d 0 1) (by simp) with h1053 | h1053
                    · rcases p1049_3 (m.d 0 2) (by simp) with h1054 | h1054
                      · linarith only [h0, h1054, hlam]
                      · linarith only [h1054, h5, hlam]
                    · linarith only [h1053, h2, hlam]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1043, h6, h785, h786, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h0, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1043, h1044, h4, h785, h786, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    rcases p1049_3 (m.d 0 1) (by simp) with h1062 | h1062
                    · rcases p1049_3 (m.d 0 2) (by simp) with h1063 | h1063
                      · rcases p1049_3 (m.d 0 3) (by simp) with h1064 | h1064
                        · linarith only [h1064, h4, hlam]
                        · linarith only [h1064, h7, hlam]
                      · linarith only [h1063, h5, hlam]
                    · linarith only [h1062, h2, hlam]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h0, h1043, h6, h785, h786, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1, hlam, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h4, hlam, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    rcases p1049_3 (m.d 0 1) (by simp) with h1073 | h1073
                    · rcases p1049_3 (m.d 0 2) (by simp) with h1074 | h1074
                      · rcases p1049_3 (m.d 0 3) (by simp) with h1075 | h1075
                        · rcases p1049_3 (m.d 0 4) (by simp) with h1076 | h1076
                          · linarith only [h1076, h7, hlam]
                          · rcases p1049_3 (m.d 0 5) (by simp) with h1078 | h1078
                            · linarith only [h1078, h8, hlam]
                            · linarith only [h1078, h9, hlam]
                        · linarith only [h1075, h7, hlam]
                      · linarith only [h1074, h5, hlam]
                    · linarith only [h1073, h2, hlam]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h1043, h6, h785, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1049_1, u3elo0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h2, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h5, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h7, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h9, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h3, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h6, hlam, p1049_1]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [h8, hlam, p1049_0]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    rcases p1049_3 (m.d 0 1) (by simp) with h1093 | h1093
                    · rcases p1049_3 (m.d 0 2) (by simp) with h1094 | h1094
                      · rcases p1049_3 (m.d 0 3) (by simp) with h1095 | h1095
                        · rcases p1049_3 (m.d 0 4) (by simp) with h1096 | h1096
                          · linarith only [h1096, h9, hlam]
                          · rcases p1049_3 (m.d 0 5) (by simp) with h1098 | h1098
                            · rcases h0emin with h1099 | h1099 | h1099 | h1099 | h1099
                              · rcases h2bigk with h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c | h1100c
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  rcases p1100_3 (m.d 0 2) (by simp) with h1102 | h1102
                                  · rcases p1100_3 (m.d 1 2) (by simp) with h1103 | h1103
                                    · linarith only [h0, h1103, hlam]
                                    · rcases p1100_3 (m.d 2 3) (by simp) with h1105 | h1105
                                      · linarith only [h1105, h4, hlam]
                                      · linarith only [h1105, h369, hlam]
                                  · linarith only [h0, h1102, hlam]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h0, h1043, h1044, h785, h786, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1044, h4, h785, h786, hlam, p1100_2]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1043, h785, h786, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h0, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h369, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1043, h1044, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1100_1, u3elo2]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h786, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h4, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h4, hc12, hlam, hphi, ht23, p1100_1, u3elo0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  rcases p1100_3 (m.d 0 2) (by simp) with h1120 | h1120
                                  · rcases p1100_3 (m.d 1 2) (by simp) with h1121 | h1121
                                    · linarith only [h1121, h369, hlam]
                                    · linarith only [h1121, h785, hlam]
                                  · linarith only [h1120, h5, hlam]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1043, h4, h785, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1100_1, u3elo0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h5, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h785, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1043, hlam, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1045, hlam, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h6, hlam, p1100_0]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h0, h1043, h6, h785, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [h1044, hlam, p1100_1]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  rcases p1100_3 (m.d 0 2) (by simp) with h1134 | h1134
                                  · rcases p1100_3 (m.d 1 2) (by simp) with h1135 | h1135
                                    · linarith only [h1135, h786, hlam]
                                    · linarith only [h1135, h785, hlam]
                                  · linarith only [h1134, h5, hlam]
                                · have p1100_0 := h1100c.1
                                  have p1100_1 := h1100c.2.1
                                  have p1100_2 := h1100c.2.2.1
                                  have p1100_3 := h1100c.2.2.2
                                  linarith only [hlam, p1100_0]
                              · rcases h2bigk with h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c | h1140c
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  rcases p1140_3 (m.d 0 2) (by simp) with h1142 | h1142
                                  · rcases p1140_3 (m.d 1 2) (by simp) with h1143 | h1143
                                    · linarith only [h0, h1143, hlam]
                                    · rcases p1140_3 (m.d 2 3) (by simp) with h1145 | h1145
                                      · linarith only [h1145, h4, hlam]
                                      · linarith only [h1145, h369, hlam]
                                  · linarith only [h0, h1142, hlam]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h0, h1043, h369, h785, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h369, h4, h785, hlam, p1140_2]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1043, h785, h786, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h0, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h369, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1043, h369, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1140_1, u3elo2]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h786, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h4, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p1140_1, u3elo2]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  rcases p1140_3 (m.d 0 2) (by simp) with h1160 | h1160
                                  · rcases p1140_3 (m.d 1 2) (by simp) with h1161 | h1161
                                    · linarith only [h1161, h369, hlam]
                                    · linarith only [h1161, h785, hlam]
                                  · linarith only [h1160, h5, hlam]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1043, h4, h785, h786, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1140_1, u3elo0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h5, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h785, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1043, hlam, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1045, hlam, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h6, hlam, p1140_0]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h0, h1043, h6, h785, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [h1044, hlam, p1140_1]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  rcases p1140_3 (m.d 0 2) (by simp) with h1174 | h1174
                                  · rcases p1140_3 (m.d 1 2) (by simp) with h1175 | h1175
                                    · linarith only [h1175, h786, hlam]
                                    · linarith only [h1175, h785, hlam]
                                  · linarith only [h1174, h5, hlam]
                                · have p1140_0 := h1140c.1
                                  have p1140_1 := h1140c.2.1
                                  have p1140_2 := h1140c.2.2.1
                                  have p1140_3 := h1140c.2.2.2
                                  linarith only [hlam, p1140_0]
                              · linarith only [h1099, hlam, ht01, ht12, ht23, u3elo0]
                              · linarith only [h1099, hc05, hlam, p1049_1]
                              · linarith only [h1099, h8, hlam, ht01, ht12, ht23, u3elo0]
                            · linarith only [h1098, h9, hlam]
                        · linarith only [h1095, h7, hlam]
                      · linarith only [h1094, h5, hlam]
                    · linarith only [h1093, h2, hlam]
                  · have p1049_0 := h1049c.1
                    have p1049_1 := h1049c.2.1
                    have p1049_2 := h1049c.2.2.1
                    have p1049_3 := h1049c.2.2.2
                    linarith only [hlam, p1049_0]
            · linarith only [h1044, h8, hc23, hlam, hphi, u3elo0]
          · linarith only [h1043, h369, h785, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
        · linarith only [h1042, h8, hc13, hlam, hphi, u3elo0]
      · linarith only [h1041, h369, h7, h785, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1192 | h1192
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1193 | h1193
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1194 | h1194
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1195 | h1195
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1196 | h1196
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1197 | h1197
              · linarith only [h1197, h5, h9, hlam]
              · linarith only [h1192, h1197, h785, hlam]
            · linarith only [h1192, h1195, h1196, h785, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
          · linarith only [h1193, h1195, h369, hlam]
        · linarith only [h1194, h8, hc13, hlam, hphi, u3elo0]
      · linarith only [h1192, h1193, h369, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1204 | h1204
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1205 | h1205
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1207 | h1207
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1208 | h1208
              · linarith only [h1208, h5, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1210 | h1210
                · linarith only [h1204, h1210, h5, h785, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h0bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h1205, h1210, h369, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1215 | h1215
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1216 | h1216
                      · linarith only [h0, h1216, hlam]
                      · linarith only [h1216, h4, hlam]
                    · linarith only [h1, h1215, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1220 | h1220
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1221 | h1221
                      · linarith only [h0, h1221, hlam]
                      · linarith only [h1221, h5, hlam]
                    · linarith only [h1220, h2, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1225 | h1225
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1226 | h1226
                      · linarith only [h0, h1226, hlam]
                      · linarith only [h1226, h6, hlam]
                    · linarith only [h1225, h3, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h0, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1232 | h1232
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1233 | h1233
                      · rcases p1212_3 (m.d 0 3) (by simp) with h1234 | h1234
                        · linarith only [h1234, h4, hlam]
                        · rcases p1212_3 (m.d 0 4) (by simp) with h1236 | h1236
                          · linarith only [h1236, h5, hlam]
                          · rcases p1212_3 (m.d 0 5) (by simp) with h1238 | h1238
                            · linarith only [h1238, h6, hlam]
                            · rcases h0emin with h1240 | h1240 | h1240 | h1240 | h1240
                              · rcases h2bigk with h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c | h1241c
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h1207, h1208, h4, h785, hlam, p1212_1, p1241_2]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  rcases p1241_3 (m.d 0 2) (by simp) with h1244 | h1244
                                  · rcases p1241_3 (m.d 1 2) (by simp) with h1245 | h1245
                                    · linarith only [h0, h1245, hlam]
                                    · rcases p1241_3 (m.d 2 3) (by simp) with h1247 | h1247
                                      · linarith only [h1247, hlam, p1241_0]
                                      · rcases p1241_3 (m.d 2 4) (by simp) with h1249 | h1249
                                        · linarith only [h1249, h5, hlam]
                                        · rcases p1241_3 (m.d 2 5) (by simp) with h1251 | h1251
                                          · linarith only [h1251, h6, hlam]
                                          · rcases h2emin with h1253 | h1253 | h1253 | h1253 | h1253
                                            · rcases h3bigk with h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c | h1254c
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h1207, h1208, h785, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h1210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h369, hlam, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h1210, h369, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h4, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h0, h1210, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h7, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1204, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1206, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1210, hlam, p1254_1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h8, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1205, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1207, hlam, p1254_0]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [h1205, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1254_1, u3elo1]
                                              · have p1254_0 := h1254c.1
                                                have p1254_1 := h1254c.2.1
                                                have p1254_2 := h1254c.2.2.1
                                                have p1254_3 := h1254c.2.2.2
                                                linarith only [hlam, p1254_0]
                                            · linarith only [h0, h1208, h1253, h6, h785, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1253, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1208, h1253, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1253, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                  · linarith only [h1244, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  rcases p1241_3 (m.d 0 2) (by simp) with h1285 | h1285
                                  · rcases p1241_3 (m.d 1 2) (by simp) with h1286 | h1286
                                    · linarith only [h0, h1286, hlam]
                                    · rcases p1241_3 (m.d 2 3) (by simp) with h1288 | h1288
                                      · linarith only [h1288, h4, hlam]
                                      · linarith only [h1206, h1288, hlam]
                                  · linarith only [h1285, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  rcases p1241_3 (m.d 0 2) (by simp) with h1292 | h1292
                                  · rcases p1241_3 (m.d 1 2) (by simp) with h1293 | h1293
                                    · linarith only [h0, h1293, hlam]
                                    · rcases p1241_3 (m.d 2 3) (by simp) with h1295 | h1295
                                      · linarith only [h1295, h4, hlam]
                                      · linarith only [h1207, h1295, hlam]
                                  · linarith only [h1292, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h369, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h785, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h1192, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h4, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, h4, h785, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1212_1, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h5, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h1206, hlam, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h1208, hlam, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h6, hlam, p1241_0]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h1207, hlam, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1241_1]
                                · have p1241_0 := h1241c.1
                                  have p1241_1 := h1241c.2.1
                                  have p1241_2 := h1241c.2.2.1
                                  have p1241_3 := h1241c.2.2.2
                                  linarith only [hlam, p1241_0]
                              · rcases h2bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h5, h785, h8, h9, hlam, p1212_1, p1319_2]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  rcases p1319_3 (m.d 0 2) (by simp) with h1322 | h1322
                                  · rcases p1319_3 (m.d 1 2) (by simp) with h1323 | h1323
                                    · linarith only [h0, h1323, hlam]
                                    · rcases p1319_3 (m.d 2 3) (by simp) with h1325 | h1325
                                      · linarith only [h1325, hlam, p1319_0]
                                      · rcases p1319_3 (m.d 2 4) (by simp) with h1327 | h1327
                                        · linarith only [h1327, h5, hlam]
                                        · rcases p1319_3 (m.d 2 5) (by simp) with h1329 | h1329
                                          · linarith only [h1329, h6, hlam]
                                          · rcases h2emin with h1331 | h1331 | h1331 | h1331 | h1331
                                            · rcases h3bigk with h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h369, hlam, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h4, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hc13, hlam, hphi, p1332_1, u3elo2]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h7, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1204, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1206, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1210, hlam, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h8, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1205, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h1207, hlam, p1332_0]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1332_1]
                                              · have p1332_0 := h1332c.1
                                                have p1332_1 := h1332c.2.1
                                                have p1332_2 := h1332c.2.2.1
                                                have p1332_3 := h1332c.2.2.2
                                                linarith only [hlam, p1332_0]
                                            · linarith only [h0, h1331, h5, h785, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1331, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1331, h5, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                            · linarith only [h0, h1331, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1]
                                  · linarith only [h1322, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  rcases p1319_3 (m.d 0 2) (by simp) with h1363 | h1363
                                  · rcases p1319_3 (m.d 1 2) (by simp) with h1364 | h1364
                                    · linarith only [h0, h1364, hlam]
                                    · rcases p1319_3 (m.d 2 3) (by simp) with h1366 | h1366
                                      · linarith only [h1366, h4, hlam]
                                      · linarith only [h1206, h1366, hlam]
                                  · linarith only [h1363, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  rcases p1319_3 (m.d 0 2) (by simp) with h1370 | h1370
                                  · rcases p1319_3 (m.d 1 2) (by simp) with h1371 | h1371
                                    · linarith only [h0, h1371, hlam]
                                    · rcases p1319_3 (m.d 2 3) (by simp) with h1373 | h1373
                                      · linarith only [h1373, h4, hlam]
                                      · linarith only [h1207, h1373, hlam]
                                  · linarith only [h1370, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h369, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h785, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h1192, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h4, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h5, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h5, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h1206, hlam, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h1208, hlam, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h6, hlam, p1319_0]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h1207, hlam, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [h0, h6, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1212_1, p1319_1]
                                · have p1319_0 := h1319c.1
                                  have p1319_1 := h1319c.2.1
                                  have p1319_2 := h1319c.2.2.1
                                  have p1319_3 := h1319c.2.2.2
                                  linarith only [hlam, p1319_0]
                              · linarith only [h0, h1240, hc01, hlam, p1212_1]
                              · linarith only [h0, h1240, h8, h9, hc01, hlam, p1212_1]
                              · linarith only [h0, h1240, h8, hc01, hlam, p1212_1]
                      · linarith only [h1233, h4, hlam]
                    · linarith only [h1, h1232, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1402 | h1402
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1403 | h1403
                      · rcases p1212_3 (m.d 0 3) (by simp) with h1404 | h1404
                        · linarith only [h1404, h4, hlam]
                        · linarith only [h1404, h7, hlam]
                      · linarith only [h1403, h5, hlam]
                    · linarith only [h1402, h2, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    rcases p1212_3 (m.d 0 1) (by simp) with h1409 | h1409
                    · rcases p1212_3 (m.d 0 2) (by simp) with h1410 | h1410
                      · rcases p1212_3 (m.d 0 3) (by simp) with h1411 | h1411
                        · linarith only [h1411, h4, hlam]
                        · linarith only [h1411, h8, hlam]
                      · linarith only [h1410, h6, hlam]
                    · linarith only [h1409, h3, hlam]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h1, hlam, p1212_1]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h4, hlam, p1212_1]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h2, h785, hc12, hlam, hphi, ht23, p1212_1, u3elo0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h1192, h3, hc12, hlam, hphi, ht23, p1212_1, u3elo0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h2, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h5, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h7, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h9, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h3, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h6, hlam, p1212_1]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h8, hlam, p1212_0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [h5, h785, h8, hc12, hlam, hphi, ht23, p1212_1, u3elo0]
                  · have p1212_0 := h1212c.1
                    have p1212_1 := h1212c.2.1
                    have p1212_2 := h1212c.2.2.1
                    have p1212_3 := h1212c.2.2.2
                    linarith only [hlam, p1212_0]
            · linarith only [h1205, h1207, hc23, hlam, hphi, u3elo1]
          · linarith only [h1206, h369, h7, hc13, hlam, hphi, u3elo0]
        · linarith only [h1204, h1205, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
      · linarith only [h1204, h369, h7, hc12, hlam, hphi, ht23, u3elo0]

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h369 | h369
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h369
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9 h369

set_option maxHeartbeats 5076000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s4_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9

end R2N4
