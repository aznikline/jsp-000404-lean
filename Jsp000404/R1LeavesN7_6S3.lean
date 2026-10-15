import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1924 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 4 5 (by decide) (by decide) with h3858 | h3858
  · linarith only [h1923, h1924, h3858, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3860 | h3860
    · linarith only [h0, h1923, h3860, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3862 | h3862
      · linarith only [h0, h1270, h3862, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3864 | h3864
        · linarith only [h0, h1799, h3864, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3866 | h3866
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3867 | h3867
            · linarith only [h1, h1270, h3858, h3866, h3867, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3869 | h3869
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3870 | h3870
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3871 | h3871
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3872 | h3872
                    · linarith only [h1, h1270, h3858, h3866, h3872, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c | h3874c
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        rcases p3874_3 (m.d 0 1) (by simp) with h3876 | h3876
                        · rcases p3874_3 (m.d 0 2) (by simp) with h3877 | h3877
                          · linarith only [h0, h3877, hlam]
                          · rcases p3874_3 (m.d 0 3) (by simp) with h3879 | h3879
                            · linarith only [h1, h3879, hlam]
                            · linarith only [h3879, h4, hlam]
                        · linarith only [h0, h3876, hlam]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3874_1, u0elo0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        rcases p3874_3 (m.d 0 1) (by simp) with h3884 | h3884
                        · rcases p3874_3 (m.d 0 2) (by simp) with h3885 | h3885
                          · linarith only [h0, h3885, hlam]
                          · rcases p3874_3 (m.d 0 3) (by simp) with h3887 | h3887
                            · linarith only [h1, h3887, hlam]
                            · linarith only [h1923, h3887, hlam]
                        · linarith only [h2, h3884, hlam]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1, h1924, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3874_1, u0elo0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h4, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1270, hlam, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1799, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1, hlam, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, h1924, h3869, h3871, h3872, hc12, hc23, hlam, hphi, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, h1270, h1924, h3869, h3871, h3872, hc12, hc23, hlam, hphi, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1924, hlam, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h2, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, h1923, h1924, h3869, h3871, h3872, hc12, hc23, hlam, hphi, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1923, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h3858, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h3, hlam, p3874_0]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, h1924, h3869, h3871, h3872, hc12, hc23, hlam, hphi, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h1, h1924, h3866, h3869, h3871, h3872, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [h0, h1270, h1924, h3869, h3871, h3872, hc12, hc23, hlam, hphi, p3874_1]
                      · have p3874_0 := h3874c.1
                        have p3874_1 := h3874c.2.1
                        have p3874_2 := h3874c.2.2.1
                        have p3874_3 := h3874c.2.2.2
                        linarith only [hlam, p3874_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3912 | h3912
                    · linarith only [h1, h3866, h3871, h3912, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c | h3914c
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        rcases p3914_3 (m.d 0 1) (by simp) with h3916 | h3916
                        · rcases p3914_3 (m.d 0 2) (by simp) with h3917 | h3917
                          · linarith only [h0, h3917, hlam]
                          · rcases p3914_3 (m.d 0 3) (by simp) with h3919 | h3919
                            · linarith only [h1, h3919, hlam]
                            · linarith only [h3919, h4, hlam]
                        · linarith only [h0, h3916, hlam]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3914_1, u0elo0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        rcases p3914_3 (m.d 0 1) (by simp) with h3924 | h3924
                        · rcases p3914_3 (m.d 0 2) (by simp) with h3925 | h3925
                          · linarith only [h0, h3925, hlam]
                          · rcases p3914_3 (m.d 0 3) (by simp) with h3927 | h3927
                            · linarith only [h1, h3927, hlam]
                            · linarith only [h1923, h3927, hlam]
                        · linarith only [h2, h3924, hlam]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1, h1924, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3914_1, u0elo0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h4, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1270, hlam, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1799, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1, hlam, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, h1924, h3870, hc12, hc23, hlam, hphi, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, h1270, h1924, h3870, hc12, hc23, hlam, hphi, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1924, hlam, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h2, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, h1270, h3871, hc12, hc45, hlam, hphi, ht23, ht34, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1923, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h3858, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h3, hlam, p3914_0]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, h1924, h3870, hc12, hc23, hlam, hphi, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h1, h1924, h3866, h3870, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [h0, h1270, h1924, h3870, hc12, hc23, hlam, hphi, p3914_1]
                      · have p3914_0 := h3914c.1
                        have p3914_1 := h3914c.2.1
                        have p3914_2 := h3914c.2.2.1
                        have p3914_3 := h3914c.2.2.2
                        linarith only [hlam, p3914_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3952 | h3952
                  · linarith only [h0, h1270, h3858, h3869, h3870, h3952, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3954 | h3954
                    · linarith only [h0, h1, h1270, h3866, h3952, h3954, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c | h3956c
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        rcases p3956_3 (m.d 0 1) (by simp) with h3958 | h3958
                        · rcases p3956_3 (m.d 0 2) (by simp) with h3959 | h3959
                          · linarith only [h0, h3959, hlam]
                          · rcases p3956_3 (m.d 0 3) (by simp) with h3961 | h3961
                            · linarith only [h1, h3961, hlam]
                            · linarith only [h3961, h4, hlam]
                        · linarith only [h0, h3958, hlam]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3956_1, u0elo0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        rcases p3956_3 (m.d 0 1) (by simp) with h3966 | h3966
                        · rcases p3956_3 (m.d 0 2) (by simp) with h3967 | h3967
                          · linarith only [h0, h3967, hlam]
                          · rcases p3956_3 (m.d 0 3) (by simp) with h3969 | h3969
                            · linarith only [h1, h3969, hlam]
                            · linarith only [h1923, h3969, hlam]
                        · linarith only [h2, h3966, hlam]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1, h1924, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3956_1, u0elo0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h0, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h4, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1270, hlam, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1799, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1, hlam, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h0, h3870, h4, hc12, hc35, hlam, hphi, ht23, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h0, h1270, h3870, h3954, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1924, hlam, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h2, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h0, h1923, h3870, h3954, h4, hc12, hc45, hlam, hphi, ht23, ht34, p3956_1]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1923, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h3858, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h3, hlam, p3956_0]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        rcases p3956_3 (m.d 0 1) (by simp) with h3990 | h3990
                        · rcases p3956_3 (m.d 0 2) (by simp) with h3991 | h3991
                          · linarith only [h1799, h3991, hlam]
                          · rcases p3956_3 (m.d 0 3) (by simp) with h3993 | h3993
                            · linarith only [h1924, h3993, hlam]
                            · linarith only [h3993, h4, hlam]
                        · linarith only [h0, h3990, hlam]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [h1, h3866, hc34, hlam, hphi, ht0b, ht45, ht5b, p3956_1, u0elo4]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        rcases p3956_3 (m.d 0 1) (by simp) with h3998 | h3998
                        · rcases p3956_3 (m.d 0 2) (by simp) with h3999 | h3999
                          · linarith only [h1799, h3999, hlam]
                          · rcases p3956_3 (m.d 0 3) (by simp) with h4001 | h4001
                            · linarith only [h1924, h4001, hlam]
                            · linarith only [h1923, h4001, hlam]
                        · linarith only [h2, h3998, hlam]
                      · have p3956_0 := h3956c.1
                        have p3956_1 := h3956c.2.1
                        have p3956_2 := h3956c.2.2.1
                        have p3956_3 := h3956c.2.2.2
                        linarith only [hlam, p3956_0]
              · linarith only [h1, h3866, h3869, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h1923, h1924, h3866, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 3 5 (by decide) (by decide) with h1924 | h1924
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s6_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 hg4 hg1270 hg1799 h1923 h1924

set_option maxHeartbeats 6068000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1270 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1799 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1923 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4008 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1270 := hg1270
  have h1799 := hg1799
  rcases m.htr 0 4 5 (by decide) (by decide) with h4009 | h4009
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4010 | h4010
    · linarith only [h0, h4, h4008, h4010, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4012 | h4012
      · linarith only [h0, h1270, h4012, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4014 | h4014
        · linarith only [h0, h1799, h4014, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4016 | h4016
          · linarith only [h1, h1923, h4008, h4016, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4018 | h4018
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4019 | h4019
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4020 | h4020
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4021 | h4021
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4022 | h4022
                    · rcases h0bigk with h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        rcases p4023_3 (m.d 0 1) (by simp) with h4025 | h4025
                        · rcases p4023_3 (m.d 0 2) (by simp) with h4026 | h4026
                          · linarith only [h0, h4026, hlam]
                          · rcases p4023_3 (m.d 0 3) (by simp) with h4028 | h4028
                            · linarith only [h1, h4028, hlam]
                            · linarith only [h4, h4028, hlam]
                        · linarith only [h0, h4025, hlam]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h4008, h4022, hc45, hlam, hphi, ht0b, ht5b, p4023_1, u0elo0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h1923, h4008, h4022, hc45, hlam, hphi, ht0b, ht5b, p4023_1, u0elo0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        rcases p4023_3 (m.d 0 1) (by simp) with h4034 | h4034
                        · rcases p4023_3 (m.d 0 2) (by simp) with h4035 | h4035
                          · linarith only [h0, h4035, hlam]
                          · rcases p4023_3 (m.d 0 3) (by simp) with h4037 | h4037
                            · linarith only [h1, h4037, hlam]
                            · linarith only [h4008, h4037, hlam]
                        · linarith only [h3, h4034, hlam]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h4, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h1270, hlam, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h1799, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h1, hlam, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1923, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h1923, hlam, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1799, h1923, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h2, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1923, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1923, h4, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1799, h1923, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h3, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h0, h1923, h4008, h4019, hc12, hc23, hlam, hphi, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h4008, hlam, p4023_0]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [h4009, hlam, p4023_1]
                      · have p4023_0 := h4023c.1
                        have p4023_1 := h4023c.2.1
                        have p4023_2 := h4023c.2.2.1
                        have p4023_3 := h4023c.2.2.2
                        linarith only [hlam, p4023_0]
                    · linarith only [h1923, h4009, h4022, hlam]
                  · linarith only [h1923, h3, h4008, h4018, h4019, h4021, hlam]
                · linarith only [h1923, h4008, h4020, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4064 | h4064
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4065 | h4065
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4066 | h4066
                    · rcases h0bigk with h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c | h4067c
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        rcases p4067_3 (m.d 0 1) (by simp) with h4069 | h4069
                        · rcases p4067_3 (m.d 0 2) (by simp) with h4070 | h4070
                          · linarith only [h0, h4070, hlam]
                          · rcases p4067_3 (m.d 0 3) (by simp) with h4072 | h4072
                            · linarith only [h1, h4072, hlam]
                            · linarith only [h4, h4072, hlam]
                        · linarith only [h0, h4069, hlam]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h4008, hc35, hlam, hphi, ht0b, ht5b, p4067_1, u0elo0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h2, h4018, hc45, hlam, hphi, ht0b, ht5b, p4067_1, u0elo0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        rcases p4067_3 (m.d 0 1) (by simp) with h4078 | h4078
                        · rcases p4067_3 (m.d 0 2) (by simp) with h4079 | h4079
                          · linarith only [h0, h4079, hlam]
                          · rcases p4067_3 (m.d 0 3) (by simp) with h4081 | h4081
                            · linarith only [h1, h4081, hlam]
                            · linarith only [h4008, h4081, hlam]
                        · linarith only [h3, h4078, hlam]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h0, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h4, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h1270, hlam, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h1799, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h1, hlam, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h0, h4, h4019, hc12, hc34, hlam, hphi, ht23, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h1923, hlam, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h0, h1799, h4, h4019, hc12, hc34, hlam, hphi, ht23, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h2, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        rcases p4067_3 (m.d 0 1) (by simp) with h4096 | h4096
                        · rcases p4067_3 (m.d 0 2) (by simp) with h4097 | h4097
                          · linarith only [h1270, h4097, hlam]
                          · rcases p4067_3 (m.d 0 3) (by simp) with h4099 | h4099
                            · linarith only [h1923, h4099, hlam]
                            · linarith only [h4, h4099, hlam]
                        · linarith only [h0, h4096, hlam]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h2, h4008, h4066, hc45, hlam, hphi, ht0b, ht5b, p4067_1, u0elo0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        rcases p4067_3 (m.d 0 1) (by simp) with h4105 | h4105
                        · rcases p4067_3 (m.d 0 2) (by simp) with h4106 | h4106
                          · linarith only [h1270, h4106, hlam]
                          · rcases p4067_3 (m.d 0 3) (by simp) with h4108 | h4108
                            · linarith only [h1923, h4108, hlam]
                            · linarith only [h4008, h4108, hlam]
                        · linarith only [h3, h4105, hlam]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h3, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h0, h4, h4008, h4019, hc12, hc34, hlam, hphi, ht23, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h4008, hlam, p4067_0]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [h4009, hlam, p4067_1]
                      · have p4067_0 := h4067c.1
                        have p4067_1 := h4067c.2.1
                        have p4067_2 := h4067c.2.2.1
                        have p4067_3 := h4067c.2.2.2
                        linarith only [hlam, p4067_0]
                    · linarith only [h2, h4, h4018, h4019, h4066, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1270, h3, h4018, h4065, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h4, h4008, h4064, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4120 | h4120
              · linarith only [h1923, h4008, h4009, h4012, h4018, h4120, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4122 | h4122
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4123 | h4123
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4124 | h4124
                    · linarith only [h4, h4008, h4010, h4016, h4018, h4120, h4124, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h4008, h4009, h4120, h4124, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h0, h1270, h4, h4008, h4009, h4120, h4123, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h4, h4008, h4122, hlam]
  · linarith only [h1923, h4008, h4009, hlam]

end R2N4
