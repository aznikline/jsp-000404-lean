import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4818 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4819 | h4819
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4820 | h4820
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4821 | h4821
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4822 | h4822
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4823 | h4823
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4824 | h4824
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4825 | h4825
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4826 | h4826
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4827 | h4827
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4828 | h4828
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4829 | h4829
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4830 | h4830
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4831 | h4831
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4832 | h4832
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4833 | h4833
                              · linarith only [h4819, h4830, h4833, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h4439, h4818, h4825, h4827, h4829, h4833, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h4439, h4818, h4825, h4827, h4829, h4832, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h4439, h4818, h4825, h4827, h4828, h4831, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4838 | h4838
                          · linarith only [h4822, h4830, h4838, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h4439, h4818, h4825, h4827, h4828, h4838, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h4439, h4824, h4829, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h3888, h4823, h4828, hlam]
                  · linarith only [h3888, h4822, h4827, hlam]
                · linarith only [h0, h4820, h4826, hlam]
              · linarith only [h0, h4819, h4825, hlam]
            · linarith only [h4439, h4818, h4824, hlam]
          · linarith only [h3888, h4818, h4823, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4848 | h4848
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4849 | h4849
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4850 | h4850
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4851 | h4851
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4852 | h4852
                  · linarith only [h3888, h4822, h4850, h4852, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4854 | h4854
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4855 | h4855
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4856 | h4856
                        · linarith only [h4819, h4822, h4856, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4858 | h4858
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4859 | h4859
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4860 | h4860
                              · rcases h0bigk with h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c | h4861c
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h0, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h3888, hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4439, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h3888, hc05, hlam, hphi, ht01, ht0b, ht5b, p4861_1, u1elo2]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p4861_1, u1elo1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h0, h3888, h4818, hc15, hlam, hphi, ht01, ht0b, ht5b, p4861_1, u1elo1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h0, h4439, h4818, hc15, hlam, hphi, ht01, ht0b, ht5b, p4861_1, u1elo1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  rcases p4861_3 (m.d 0 1) (by simp) with h4871 | h4871
                                  · linarith only [h0, h4871, hlam]
                                  · linarith only [h4818, h4871, hlam]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4818, hc15, hlam, hphi, ht0b, ht5b, p4861_1, u0elo2]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4819, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4822, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  rcases p4861_3 (m.d 0 1) (by simp) with h4878 | h4878
                                  · linarith only [h3888, h4878, hlam]
                                  · linarith only [h4818, h4878, hlam]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4439, h4851, hc01, hlam, hphi, p4861_1, u1elo1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4820, hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h3888, h4439, h4818, h4851, h4854, h4860, hc45, hlam, hphi, ht01, ht0b, ht5b, p4861_1, u1elo1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  rcases p4861_3 (m.d 0 1) (by simp) with h4885 | h4885
                                  · linarith only [h4439, h4885, hlam]
                                  · linarith only [h4818, h4885, hlam]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4818, hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4821, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4848, hlam, p4861_0]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [h4849, hlam, p4861_1]
                                · have p4861_0 := h4861c.1
                                  have p4861_1 := h4861c.2.1
                                  have p4861_2 := h4861c.2.2.1
                                  have p4861_3 := h4861c.2.2.2
                                  linarith only [hlam, p4861_0]
                              · linarith only [h3888, h4852, h4860, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h3888, h4818, h4851, h4852, h4855, h4856, h4859, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h3888, h4818, h4852, h4854, h4858, hc23, hc34, hlam, hphi]
                      · linarith only [h3888, h4849, h4852, h4855, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h3888, h4848, h4854, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h4820, h4851, hlam]
              · linarith only [h0, h4819, h4850, hlam]
            · linarith only [h3888, h4818, h4822, h4849, hlam]
          · linarith only [h3888, h4818, h4848, hlam]
      · linarith only [h0, h4818, h4821, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4903 | h4903
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4904 | h4904
        · linarith only [h4819, h4820, h4904, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4906 | h4906
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4907 | h4907
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4908 | h4908
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4909 | h4909
                · linarith only [h3888, h4819, h4820, h4909, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4911 | h4911
                  · linarith only [h3888, h4818, h4904, h4911, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4913 | h4913
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4914 | h4914
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4915 | h4915
                        · linarith only [h3888, h4818, h4911, h4913, h4915, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4917 | h4917
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4918 | h4918
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4919 | h4919
                              · rcases h0bigk with h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c | h4920c
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h0, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h3888, hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4439, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h3888, hc05, hlam, hphi, ht01, ht0b, ht5b, p4920_1, u1elo2]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h0, h4909, h4915, hc01, hc34, hlam, hphi, ht12, ht23, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h0, h3888, h4818, h4909, h4913, h4915, h4919, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4820, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  rcases p4920_3 (m.d 0 1) (by simp) with h4930 | h4930
                                  · linarith only [h0, h4930, hlam]
                                  · linarith only [h4818, h4930, hlam]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4818, h4913, h4919, hc45, hlam, hphi, ht0b, ht5b, p4920_1, u0elo2]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4819, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4904, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  rcases p4920_3 (m.d 0 1) (by simp) with h4937 | h4937
                                  · linarith only [h3888, h4937, hlam]
                                  · linarith only [h4818, h4937, hlam]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4818, h4913, h4919, hc45, hlam, hphi, ht0b, ht5b, p4920_1, u0elo3]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h0, h4439, h4818, h4913, h4919, hc45, hlam, hphi, ht01, ht0b, ht5b, p4920_1, u1elo3]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h3888, h4439, h4818, h4913, h4919, hc45, hlam, hphi, ht01, ht0b, ht5b, p4920_1, u1elo3]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  rcases p4920_3 (m.d 0 1) (by simp) with h4944 | h4944
                                  · linarith only [h4439, h4944, hlam]
                                  · linarith only [h4818, h4944, hlam]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4818, hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4903, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4906, hlam, p4920_0]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [h4907, hlam, p4920_1]
                                · have p4920_0 := h4920c.1
                                  have p4920_1 := h4920c.2.1
                                  have p4920_2 := h4920c.2.2.1
                                  have p4920_3 := h4920c.2.2.2
                                  linarith only [hlam, p4920_0]
                              · linarith only [h0, h4818, h4909, h4915, h4919, hc15, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h3888, h4818, h4908, h4909, h4913, h4918, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h3888, h4818, h4908, h4913, h4917, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h4439, h4818, h4907, h4914, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                    · linarith only [h0, h3888, h4818, h4819, h4906, h4909, h4913, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h4819, h4908, hlam]
            · linarith only [h0, h4818, h4820, h4907, hlam]
          · linarith only [h3888, h4818, h4906, hlam]
      · linarith only [h3888, h4818, h4819, h4903, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4961 | h4961
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4962 | h4962
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4963 | h4963
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4964 | h4964
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4965 | h4965
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4966 | h4966
              · linarith only [h4439, h4819, h4961, h4966, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4968 | h4968
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4969 | h4969
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4970 | h4970
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4971 | h4971
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4972 | h4972
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4973 | h4973
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4974 | h4974
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4975 | h4975
                              · rcases h0bigk with h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c | h4976c
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h0, hlam, p4976_1]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h3888, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4439, hlam, p4976_1]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4439, h4966, h4968, hc05, hlam, hphi, ht01, ht0b, ht5b, p4976_1, u1elo2]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4818, h4819, hc15, hlam, hphi, ht0b, ht5b, p4976_1, u0elo2]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4819, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4439, h4818, h4970, hc35, hlam, hphi, ht0b, ht5b, p4976_1, u0elo1]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  rcases p4976_3 (m.d 0 1) (by simp) with h4986 | h4986
                                  · linarith only [h0, h4986, hlam]
                                  · linarith only [h4818, h4986, hlam]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h3888, h4818, h4970, h4975, hc45, hlam, hphi, ht01, ht0b, ht5b, p4976_1, u1elo2]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h0, h3888, h4818, h4970, h4975, hc45, hlam, hphi, ht01, ht0b, ht5b, p4976_1, u1elo2]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h3888, h4439, h4818, h4970, h4975, hc45, hlam, hphi, ht01, ht0b, ht5b, p4976_1, u1elo2]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  rcases p4976_3 (m.d 0 1) (by simp) with h4993 | h4993
                                  · linarith only [h3888, h4993, hlam]
                                  · linarith only [h4818, h4993, hlam]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4818, h4970, h4975, hc45, hlam, hphi, ht0b, ht5b, p4976_1, u0elo3]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4961, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4963, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  rcases p4976_3 (m.d 0 1) (by simp) with h5000 | h5000
                                  · linarith only [h4439, h5000, hlam]
                                  · linarith only [h4818, h5000, hlam]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4818, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4962, hlam, p4976_1]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4964, hlam, p4976_0]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [h4965, hlam, p4976_1]
                                · have p4976_0 := h4976c.1
                                  have p4976_1 := h4976c.2.1
                                  have p4976_2 := h4976c.2.2.1
                                  have p4976_3 := h4976c.2.2.2
                                  linarith only [hlam, p4976_0]
                              · linarith only [h0, h4818, h4966, h4971, h4975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h4439, h4818, h4966, h4968, h4971, h4974, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h4439, h4966, h4968, h4973, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h4439, h4818, h4966, h4968, h4971, h4972, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4439, h4965, h4971, hlam]
                    · linarith only [h3888, h4964, h4970, hlam]
                  · linarith only [h3888, h4963, h4969, hlam]
                · linarith only [h0, h3888, h4819, h4961, h4968, hc01, hlam, hphi, u1elo2]
            · linarith only [h4439, h4818, h4965, hlam]
          · linarith only [h0, h4818, h4819, h4964, hlam]
        · linarith only [h4819, h4961, h4963, hlam]
      · linarith only [h4439, h4818, h4961, h4962, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5020 | h5020
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5021 | h5021
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5022 | h5022
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5023 | h5023
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5024 | h5024
              · linarith only [h4819, h5020, h5024, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5026 | h5026
                · linarith only [h0, h4818, h4961, h5026, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5028 | h5028
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5029 | h5029
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5030 | h5030
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5031 | h5031
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5032 | h5032
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5033 | h5033
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5034 | h5034
                              · rcases h0bigk with h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, hlam, p5035_1]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h3888, hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4439, hlam, p5035_1]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, h5026, h5028, hc05, hlam, hphi, ht01, ht0b, ht5b, p5035_1, u1elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, h5026, h5028, hc01, hlam, hphi, p5035_1, u1elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4819, hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4961, hlam, p5035_1]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  rcases p5035_3 (m.d 0 1) (by simp) with h5045 | h5045
                                  · linarith only [h0, h5045, hlam]
                                  · linarith only [h4818, h5045, hlam]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4818, h5029, h5034, hc45, hlam, hphi, ht0b, ht5b, p5035_1, u0elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, h3888, h4818, h5029, h5034, hc45, hlam, hphi, ht01, ht0b, ht5b, p5035_1, u1elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, h3888, h4818, h4961, h5029, h5034, hc45, hlam, hphi, ht01, ht0b, ht5b, p5035_1, u1elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  rcases p5035_3 (m.d 0 1) (by simp) with h5052 | h5052
                                  · linarith only [h3888, h5052, hlam]
                                  · linarith only [h4818, h5052, hlam]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4818, h5029, h5034, hc45, hlam, hphi, ht0b, ht5b, p5035_1, u0elo3]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h0, h4439, h4818, h5028, h5029, h5034, hc45, hlam, hphi, ht01, ht0b, ht5b, p5035_1, u1elo2]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h5021, hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  rcases p5035_3 (m.d 0 1) (by simp) with h5059 | h5059
                                  · linarith only [h4439, h5059, hlam]
                                  · linarith only [h4818, h5059, hlam]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h4818, hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h5020, hlam, p5035_1]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h5022, hlam, p5035_0]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [h5023, hlam, p5035_1]
                                · have p5035_0 := h5035c.1
                                  have p5035_1 := h5035c.2.1
                                  have p5035_2 := h5035c.2.2.1
                                  have p5035_3 := h5035c.2.2.2
                                  linarith only [hlam, p5035_0]
                              · linarith only [h0, h4818, h5026, h5028, h5030, h5034, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · linarith only [h0, h4818, h5026, h5030, h5033, hlam]
                          · linarith only [h4819, h5022, h5032, hlam]
                        · linarith only [h0, h5024, h5031, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4818, h5021, h5023, h5026, h5029, h5030, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h3888, h4818, h5022, h5029, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h0, h5021, h5024, h5028, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h4818, h4961, h5023, hlam]
          · linarith only [h3888, h4818, h5022, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5076 | h5076
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5077 | h5077
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5078 | h5078
              · linarith only [h0, h4819, h5078, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5080 | h5080
                · linarith only [h0, h4818, h4961, h5080, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5082 | h5082
                  · linarith only [h0, h4818, h4819, h5021, h5082, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5084 | h5084
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5085 | h5085
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5086 | h5086
                        · linarith only [h0, h4818, h5078, h5082, h5084, h5086, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h4818, h5078, h5084, h5086, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4439, h4818, h5077, h5084, h5085, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h3888, h5076, h5084, hlam]
            · linarith only [h4439, h4818, h5077, hlam]
          · linarith only [h3888, h4818, h5076, hlam]
      · linarith only [h0, h4818, h5020, hlam]

end R2N4
