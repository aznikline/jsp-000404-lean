import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S8
import Jsp000404.R1LeavesN7_5S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5835 | h5835
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5836 | h5836
    · linarith only [h0, h1, h5836, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5838 | h5838
      · linarith only [h0, h4899, h5838, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5840 | h5840
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5841 | h5841
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5842 | h5842
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5843 | h5843
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5844 | h5844
                · linarith only [h0, h4899, h5836, h5840, h5841, h5844, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5846 | h5846
                  · linarith only [h0, h4899, h5838, h5846, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5848 | h5848
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5849 | h5849
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5850 | h5850
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5851 | h5851
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5852 | h5852
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5853 | h5853
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5854 | h5854
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5855 | h5855
                                  · rcases h0bigk with h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h4899, h5844, h5849, hc02, hc23, hlam, hphi, p5856_1]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h1, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h4899, hlam, p5856_1]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      rcases p5856_3 (m.d 0 1) (by simp) with h5861 | h5861
                                      · rcases p5856_3 (m.d 0 2) (by simp) with h5862 | h5862
                                        · linarith only [h0, h5862, hlam]
                                        · linarith only [h5840, h5862, hlam]
                                      · linarith only [h5835, h5861, hlam]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5836, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5838, hlam, p5856_1]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      rcases p5856_3 (m.d 0 1) (by simp) with h5870 | h5870
                                      · rcases p5856_3 (m.d 0 2) (by simp) with h5871 | h5871
                                        · rcases p5856_3 (m.d 0 3) (by simp) with h5872 | h5872
                                          · rcases p5856_3 (m.d 0 4) (by simp) with h5873 | h5873
                                            · rcases p5856_3 (m.d 0 5) (by simp) with h5874 | h5874
                                              · linarith only [h5840, h5874, hlam]
                                              · rcases h0emin with h5876 | h5876 | h5876 | h5876 | h5876
                                                · rcases h1bigk with h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c | h5877c
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h4899, h5844, h5849, hc12, hc23, hlam, hphi, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h1, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h4899, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    rcases p5877_3 (m.d 0 1) (by simp) with h5882 | h5882
                                                    · rcases p5877_3 (m.d 1 2) (by simp) with h5883 | h5883
                                                      · linarith only [h0, h5883, hlam]
                                                      · linarith only [h5848, h5883, hlam]
                                                    · linarith only [h5882, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5844, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5846, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, h4899, h5844, h5848, h5849, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5844, h5876, hc23, hlam, ht01, ht12, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    rcases p5877_3 (m.d 0 1) (by simp) with h5893 | h5893
                                                    · linarith only [h1, h5893, hlam]
                                                    · linarith only [h0, h5893, hlam]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, h4899, h5835, h5844, h5848, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5856_1, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, h1, h5835, hlam, p5856_1, p5877_2]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, h5835, h5848, h5853, h5855, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5856_1, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    rcases p5877_3 (m.d 0 1) (by simp) with h5900 | h5900
                                                    · linarith only [h4899, h5900, hlam]
                                                    · linarith only [h0, h5900, hlam]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5849, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h0, h4899, h5835, hlam, p5856_1, p5877_2]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5835, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5848, hlam, p5877_1]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5850, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [h5851, hlam, p5877_0]
                                                  · have p5877_0 := h5877c.1
                                                    have p5877_1 := h5877c.2.1
                                                    have p5877_2 := h5877c.2.2.1
                                                    have p5877_3 := h5877c.2.2.2
                                                    linarith only [hlam, p5877_0]
                                                · rcases h1bigk with h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c | h5911c
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h4899, h5844, h5849, hc12, hc23, hlam, hphi, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h1, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h4899, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    rcases p5911_3 (m.d 0 1) (by simp) with h5916 | h5916
                                                    · rcases p5911_3 (m.d 1 2) (by simp) with h5917 | h5917
                                                      · linarith only [h0, h5917, hlam]
                                                      · linarith only [h5848, h5917, hlam]
                                                    · linarith only [h5916, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5844, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5846, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h4899, h5844, h5848, h5849, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h5844, hc12, hc23, hlam, hphi, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    rcases p5911_3 (m.d 0 1) (by simp) with h5927 | h5927
                                                    · linarith only [h1, h5927, hlam]
                                                    · linarith only [h0, h5927, hlam]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h4899, h5835, h5844, h5848, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5856_1, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h1, h5835, hlam, p5856_1, p5911_2]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h5835, h5848, h5853, h5855, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5856_1, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    rcases p5911_3 (m.d 0 1) (by simp) with h5934 | h5934
                                                    · linarith only [h4899, h5934, hlam]
                                                    · linarith only [h0, h5934, hlam]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5849, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h0, h4899, h5835, hlam, p5856_1, p5911_2]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5835, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5848, hlam, p5911_1]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5850, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [h5851, hlam, p5911_0]
                                                  · have p5911_0 := h5911c.1
                                                    have p5911_1 := h5911c.2.1
                                                    have p5911_2 := h5911c.2.2.1
                                                    have p5911_3 := h5911c.2.2.2
                                                    linarith only [hlam, p5911_0]
                                                · rcases h1bigk with h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5945_1, u0elo0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h1, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h4899, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    rcases p5945_3 (m.d 0 1) (by simp) with h5950 | h5950
                                                    · rcases p5945_3 (m.d 1 2) (by simp) with h5951 | h5951
                                                      · linarith only [h0, h5951, hlam]
                                                      · linarith only [h5848, h5951, hlam]
                                                    · linarith only [h5950, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5844, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5846, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h4899, h5846, h5848, h5852, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5945_1]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h5844, hc12, hc23, hlam, hphi, p5945_1]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    rcases p5945_3 (m.d 0 1) (by simp) with h5961 | h5961
                                                    · linarith only [h1, h5961, hlam]
                                                    · linarith only [h0, h5961, hlam]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h4899, h5835, h5844, h5848, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5856_1, p5945_1]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h1, h5835, hlam, p5856_1, p5945_2]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h5835, h5848, h5853, h5855, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5856_1, p5945_1]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    rcases p5945_3 (m.d 0 1) (by simp) with h5968 | h5968
                                                    · linarith only [h4899, h5968, hlam]
                                                    · linarith only [h0, h5968, hlam]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5849, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h0, h4899, h5835, hlam, p5856_1, p5945_2]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5835, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5848, hlam, p5945_1]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5850, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [h5851, hlam, p5945_0]
                                                  · have p5945_0 := h5945c.1
                                                    have p5945_1 := h5945c.2.1
                                                    have p5945_2 := h5945c.2.2.1
                                                    have p5945_3 := h5945c.2.2.2
                                                    linarith only [hlam, p5945_0]
                                                · rcases h1bigk with h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c | h5979c
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5979_1, u0elo0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h1, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h4899, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    rcases p5979_3 (m.d 0 1) (by simp) with h5984 | h5984
                                                    · rcases p5979_3 (m.d 1 2) (by simp) with h5985 | h5985
                                                      · linarith only [h0, h5985, hlam]
                                                      · linarith only [h5848, h5985, hlam]
                                                    · linarith only [h5984, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5844, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5846, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h4899, h5844, h5848, h5849, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5979_1]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h5844, hc12, hc23, hlam, hphi, p5979_1]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    rcases p5979_3 (m.d 0 1) (by simp) with h5995 | h5995
                                                    · linarith only [h1, h5995, hlam]
                                                    · linarith only [h0, h5995, hlam]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h4899, h5835, h5844, h5848, h5853, h5855, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5856_1, p5979_1]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h1, h5835, hlam, p5856_1, p5979_2]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h5835, h5848, h5853, h5855, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5856_1, p5979_1]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    rcases p5979_3 (m.d 0 1) (by simp) with h6002 | h6002
                                                    · linarith only [h4899, h6002, hlam]
                                                    · linarith only [h0, h6002, hlam]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5849, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h0, h4899, h5835, hlam, p5856_1, p5979_2]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5835, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5848, hlam, p5979_1]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5850, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [h5851, hlam, p5979_0]
                                                  · have p5979_0 := h5979c.1
                                                    have p5979_1 := h5979c.2.1
                                                    have p5979_2 := h5979c.2.2.1
                                                    have p5979_3 := h5979c.2.2.2
                                                    linarith only [hlam, p5979_0]
                                                · linarith only [h0, h5876, hlam, p5856_1, u0elo0]
                                            · linarith only [h5843, h5873, hlam]
                                          · linarith only [h5842, h5872, hlam]
                                        · linarith only [h5840, h5871, hlam]
                                      · linarith only [h5835, h5870, hlam]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5856_1, u0elo2]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5856_1, u0elo2]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, h4899, h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5856_1, u0elo2]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      rcases p5856_3 (m.d 0 1) (by simp) with h6022 | h6022
                                      · linarith only [h1, h6022, hlam]
                                      · linarith only [h5835, h6022, hlam]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5856_1, u0elo3]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h0, h5848, h5853, h5855, hc45, hlam, hphi, ht0b, ht5b, p5856_1, u0elo3]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5841, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      rcases p5856_3 (m.d 0 1) (by simp) with h6029 | h6029
                                      · linarith only [h4899, h6029, hlam]
                                      · linarith only [h5835, h6029, hlam]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5835, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5840, hlam, p5856_1]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5842, hlam, p5856_0]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [h5843, hlam, p5856_1]
                                    · have p5856_0 := h5856c.1
                                      have p5856_1 := h5856c.2.1
                                      have p5856_2 := h5856c.2.2.1
                                      have p5856_3 := h5856c.2.2.2
                                      linarith only [hlam, p5856_0]
                                  · linarith only [h0, h4899, h5846, h5848, h5852, h5854, h5855, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h4899, h5835, h5846, h5851, h5854, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h0, h4899, h5846, h5848, h5852, h5853, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h5836, h5841, h5852, hlam]
                          · linarith only [h0, h4899, h5840, h5843, h5848, h5851, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h0, h4899, h5840, h5842, h5849, h5850, hlam]
                      · linarith only [h0, h1, h5841, h5848, h5849, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h4899, h5840, h5846, h5848, hc12, hc24, hlam, hphi]
              · linarith only [h0, h4899, h5840, h5843, hlam]
            · linarith only [h0, h4899, h5840, h5841, h5842, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6047 | h6047
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6048 | h6048
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6049 | h6049
                · linarith only [h0, h5836, h6049, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6051 | h6051
                  · linarith only [h0, h5838, h6051, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6053 | h6053
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6054 | h6054
                      · linarith only [h0, h1, h5841, h6049, h6054, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6053, h6054, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h4899, h5840, h6051, h6053, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h5840, h5841, h6048, hlam]
            · linarith only [h0, h1, h5840, h6047, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6060 | h6060
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6061 | h6061
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6062 | h6062
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6063 | h6063
                · linarith only [h0, h5836, h6063, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6065 | h6065
                  · linarith only [h0, h5838, h6065, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6067 | h6067
                    · linarith only [h0, h5840, h6067, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6069 | h6069
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6070 | h6070
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6071 | h6071
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6072 | h6072
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6073 | h6073
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6074 | h6074
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6075 | h6075
                                  · rcases h0bigk with h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c | h6076c
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h4899, h6063, h6069, hc02, hc23, hlam, hphi, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h1, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h4899, hlam, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h0, h4899, h5840, h6063, h6069, hc12, hc23, hlam, hphi, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h0, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h5836, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h5838, hlam, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h5840, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6076_1, u0elo2]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      rcases p6076_3 (m.d 0 1) (by simp) with h6088 | h6088
                                      · linarith only [h1, h6088, hlam]
                                      · linarith only [h0, h6088, hlam]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h4899, h5835, h6067, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6076_1, u0elo2]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      rcases p6076_3 (m.d 0 1) (by simp) with h6093 | h6093
                                      · linarith only [h1, h6093, hlam]
                                      · linarith only [h5835, h6093, hlam]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h5835, h6067, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6076_1, u0elo3]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      rcases p6076_3 (m.d 0 1) (by simp) with h6097 | h6097
                                      · linarith only [h4899, h6097, hlam]
                                      · linarith only [h0, h6097, hlam]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h6060, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      rcases p6076_3 (m.d 0 1) (by simp) with h6102 | h6102
                                      · linarith only [h4899, h6102, hlam]
                                      · linarith only [h5835, h6102, hlam]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h5835, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h0, h1, h5835, h6063, hc12, hc23, hlam, hphi, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h6061, hlam, p6076_0]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [h6062, hlam, p6076_1]
                                    · have p6076_0 := h6076c.1
                                      have p6076_1 := h6076c.2.1
                                      have p6076_2 := h6076c.2.2.1
                                      have p6076_3 := h6076c.2.2.2
                                      linarith only [hlam, p6076_0]
                                  · rcases h0bigk with h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h0, h4899, h6063, h6069, hc12, hc23, hlam, hphi, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h1, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h4899, hlam, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h4899, h5835, h6063, h6069, h6071, h6075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h0, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5836, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5838, hlam, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5840, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6110_1, u0elo2]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      rcases p6110_3 (m.d 0 1) (by simp) with h6122 | h6122
                                      · linarith only [h1, h6122, hlam]
                                      · linarith only [h0, h6122, hlam]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h4899, h5835, h6071, h6075, hc34, hlam, hphi, ht0b, ht45, ht5b, p6110_1, u0elo2]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5835, h6071, h6075, hc34, hlam, hphi, ht0b, ht45, ht5b, p6110_1, u0elo2]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5835, h6071, h6075, hc34, hlam, hphi, ht0b, ht45, ht5b, p6110_1, u0elo3]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      rcases p6110_3 (m.d 0 1) (by simp) with h6129 | h6129
                                      · linarith only [h4899, h6129, hlam]
                                      · linarith only [h0, h6129, hlam]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h6060, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5835, h6060, h6071, h6075, hc34, hlam, hphi, ht0b, ht45, ht5b, p6110_1, u0elo2]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h5835, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h0, h4899, h5835, h6063, h6069, hc12, hc23, hlam, hphi, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h6061, hlam, p6110_0]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [h6062, hlam, p6110_1]
                                    · have p6110_0 := h6110c.1
                                      have p6110_1 := h6110c.2.1
                                      have p6110_2 := h6110c.2.2.1
                                      have p6110_3 := h6110c.2.2.2
                                      linarith only [hlam, p6110_0]
                                · linarith only [h4899, h5835, h6065, h6071, h6074, hlam]
                              · linarith only [h0, h4899, h6063, h6069, h6073, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h4899, h6063, h6069, h6072, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h4899, h5835, h6067, h6071, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h1, h5835, h6067, h6070, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h6060, h6069, hlam]
              · linarith only [h4899, h5835, h6062, hlam]
            · linarith only [h1, h5835, h6061, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6148 | h6148
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6149 | h6149
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6150 | h6150
                · linarith only [h0, h1, h6060, h6150, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6152 | h6152
                  · linarith only [h0, h5838, h6152, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6154 | h6154
                    · linarith only [h0, h5840, h6154, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6156 | h6156
                      · linarith only [h1, h5835, h6060, h6150, h6154, h6156, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h5835, h6154, h6156, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h5835, h6060, h6149, hlam]
            · linarith only [h1, h5835, h6148, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6161 | h6161
    · linarith only [h0, h1, h6161, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6163 | h6163
      · linarith only [h0, h4899, h6163, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6165 | h6165
        · linarith only [h0, h5835, h6165, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6167 | h6167
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6168 | h6168
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6169 | h6169
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6170 | h6170
                · linarith only [h0, h5835, h6161, h6167, h6169, h6170, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6172 | h6172
                  · linarith only [h0, h5835, h6163, h6169, h6172, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6174 | h6174
                    · linarith only [h0, h6165, h6174, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6176 | h6176
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6177 | h6177
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6178 | h6178
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6179 | h6179
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6180 | h6180
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6181 | h6181
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6182 | h6182
                                  · rcases h0bigk with h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c | h6183c
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, h5835, h6170, h6176, h6178, hc12, hc23, hlam, hphi, p6183_1]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h1, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h4899, hlam, p6183_1]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h5835, hlam, p6183_1]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6161, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6163, hlam, p6183_1]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6165, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6183_1, u0elo2]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      rcases p6183_3 (m.d 0 1) (by simp) with h6195 | h6195
                                      · linarith only [h1, h6195, hlam]
                                      · linarith only [h0, h6195, hlam]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6167, h6182, hc45, hlam, hphi, ht0b, ht5b, p6183_1, u0elo2]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, h5835, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6183_1, u0elo2]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6183_1, u0elo3]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      rcases p6183_3 (m.d 0 1) (by simp) with h6202 | h6202
                                      · linarith only [h4899, h6202, hlam]
                                      · linarith only [h0, h6202, hlam]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6167, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, h5835, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6183_1, u0elo3]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6183_1, u0elo4]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      rcases p6183_3 (m.d 0 1) (by simp) with h6209 | h6209
                                      · linarith only [h5835, h6209, hlam]
                                      · linarith only [h0, h6209, hlam]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6168, hlam, p6183_0]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [h6169, hlam, p6183_1]
                                    · have p6183_0 := h6183c.1
                                      have p6183_1 := h6183c.2.1
                                      have p6183_2 := h6183c.2.2.1
                                      have p6183_3 := h6183c.2.2.2
                                      linarith only [hlam, p6183_0]
                                  · rcases h0bigk with h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c | h6215c
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, h1, h6170, hc12, hc23, hlam, hphi, p6215_1]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h1, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h4899, hlam, p6215_1]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h5835, hlam, p6215_1]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6161, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6163, hlam, p6215_1]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6165, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo2]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      rcases p6215_3 (m.d 0 1) (by simp) with h6227 | h6227
                                      · linarith only [h1, h6227, hlam]
                                      · linarith only [h0, h6227, hlam]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, h4899, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo2]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, h5835, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo2]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo3]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      rcases p6215_3 (m.d 0 1) (by simp) with h6234 | h6234
                                      · linarith only [h4899, h6234, hlam]
                                      · linarith only [h0, h6234, hlam]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6167, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, h5835, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo3]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6215_1, u0elo4]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      rcases p6215_3 (m.d 0 1) (by simp) with h6241 | h6241
                                      · linarith only [h5835, h6241, hlam]
                                      · linarith only [h0, h6241, hlam]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6168, hlam, p6215_0]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [h6169, hlam, p6215_1]
                                    · have p6215_0 := h6215c.1
                                      have p6215_1 := h6215c.2.1
                                      have p6215_2 := h6215c.2.2.1
                                      have p6215_3 := h6215c.2.2.2
                                      linarith only [hlam, p6215_0]
                                · linarith only [h0, h4899, h6172, h6181, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h0, h1, h6170, h6180, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h5835, h6170, h6176, h6178, h6179, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h4899, h6167, h6169, h6178, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h6168, h6177, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1, h6167, h6176, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6253 | h6253
                · linarith only [h0, h4899, h6169, h6253, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6255 | h6255
                  · linarith only [h0, h4899, h6169, h6255, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6257 | h6257
                    · linarith only [h0, h4899, h6165, h6169, h6257, hc02, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6259 | h6259
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6260 | h6260
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6261 | h6261
                          · linarith only [h0, h4899, h6169, h6253, h6259, h6261, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h4899, h6261, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h6168, h6260, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1, h6167, h6259, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6266 | h6266
              · linarith only [h6167, h6168, h6266, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6268 | h6268
                · linarith only [h0, h1, h6168, h6268, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6270 | h6270
                  · linarith only [h0, h4899, h6163, h6167, h6168, h6270, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6272 | h6272
                    · linarith only [h0, h6165, h6272, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6274 | h6274
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6275 | h6275
                        · linarith only [h0, h4899, h6167, h6168, h6268, h6275, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h6275, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h6167, h6274, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6279 | h6279
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6280 | h6280
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6281 | h6281
                · linarith only [h0, h6161, h6281, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6283 | h6283
                  · linarith only [h0, h6163, h6283, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6285 | h6285
                    · linarith only [h0, h5835, h6165, h6285, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6287 | h6287
                      · linarith only [h0, h5835, h6167, h6279, h6281, h6287, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6287, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h6167, h6279, h6280, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6291 | h6291
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6292 | h6292
                · linarith only [h0, h1, h6279, h6292, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6294 | h6294
                  · linarith only [h0, h6163, h6294, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6296 | h6296
                    · linarith only [h0, h6165, h6296, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6298 | h6298
                      · linarith only [h0, h1, h6167, h6292, h6298, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6298, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6301 | h6301
                · linarith only [h0, h1, h6167, h6301, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6303 | h6303
                  · linarith only [h0, h1, h6167, h6291, h6303, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6305 | h6305
                    · linarith only [h0, h6165, h6305, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6307 | h6307
                      · linarith only [h0, h1, h6167, h6301, h6307, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6307, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h4899 | h4899
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0 m hb0 hb1 hb3 hb4 hg0 h1 h4899
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x1 m hb0 hb1 hb3 hb4 hg0 h1 h4899

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x0 m hb0 hb1 hb3 hb4 hg0 h1
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1 m hb0 hb1 hb3 hb4 hg0 h1

end R2N4
