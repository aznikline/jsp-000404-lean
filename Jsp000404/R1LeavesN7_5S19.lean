import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11850 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11851 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11852 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11853 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11854 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11855 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11856 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 2 3 5 (by decide) (by decide) with h11857 | h11857
  · rcases m.htr 2 4 5 (by decide) (by decide) with h11858 | h11858
    · rcases m.htr 3 4 5 (by decide) (by decide) with h11859 | h11859
      · linarith only [h11844, h11856, h11859, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
      · linarith only [h11844, h11856, h11858, h11859, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h11862 | h11862
      · linarith only [h11844, h11847, h11858, h11862, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
      · rcases h0bigk with h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c | h11864c
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h0, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h6310, hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h9935, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11282, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          rcases p11864_3 (m.d 0 1) (by simp) with h11870 | h11870
          · linarith only [h0, h11870, hlam]
          · rcases p11864_3 (m.d 0 2) (by simp) with h11872 | h11872
            · rcases p11864_3 (m.d 0 3) (by simp) with h11873 | h11873
              · linarith only [h11844, h11873, hlam]
              · linarith only [h11873, h6310, hlam]
            · linarith only [h0, h11872, hlam]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11844, h11857, hc35, hlam, hphi, ht0b, ht5b, p11864_1, u0elo1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11849, h11856, h11858, hc34, hlam, hphi, ht0b, ht45, ht5b, p11864_1, u0elo1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11849, h11856, h11858, hc34, hlam, hphi, ht0b, ht45, ht5b, p11864_1, u0elo1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          rcases p11864_3 (m.d 0 1) (by simp) with h11881 | h11881
          · linarith only [h11881, h6310, hlam]
          · rcases p11864_3 (m.d 0 2) (by simp) with h11883 | h11883
            · rcases p11864_3 (m.d 0 3) (by simp) with h11884 | h11884
              · rcases p11864_3 (m.d 0 4) (by simp) with h11885 | h11885
                · linarith only [h11847, h11885, hlam]
                · linarith only [h11885, h9935, hlam]
              · linarith only [h11884, h6310, hlam]
            · linarith only [h0, h11883, hlam]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11844, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11849, h11856, h11858, hc34, hlam, hphi, ht0b, ht45, ht5b, p11864_1, u0elo2]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11844, h11849, h11856, h11858, hc34, hlam, hphi, ht0b, ht45, ht5b, p11864_1, u0elo1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          rcases p11864_3 (m.d 0 1) (by simp) with h11894 | h11894
          · linarith only [h11894, h9935, hlam]
          · rcases p11864_3 (m.d 0 2) (by simp) with h11896 | h11896
            · rcases p11864_3 (m.d 0 3) (by simp) with h11897 | h11897
              · rcases p11864_3 (m.d 0 4) (by simp) with h11898 | h11898
                · rcases p11864_3 (m.d 0 5) (by simp) with h11899 | h11899
                  · linarith only [h11849, h11899, hlam]
                  · linarith only [h11282, h11899, hlam]
                · linarith only [h11898, h9935, hlam]
              · linarith only [h11897, h6310, hlam]
            · linarith only [h0, h11896, hlam]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11845, hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11847, hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11849, h11856, h11858, hc34, hlam, hphi, ht0b, ht45, ht5b, p11864_1, u0elo3]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          rcases p11864_3 (m.d 0 1) (by simp) with h11909 | h11909
          · linarith only [h11282, h11909, hlam]
          · rcases p11864_3 (m.d 0 2) (by simp) with h11911 | h11911
            · rcases p11864_3 (m.d 0 3) (by simp) with h11912 | h11912
              · rcases p11864_3 (m.d 0 4) (by simp) with h11913 | h11913
                · rcases p11864_3 (m.d 0 5) (by simp) with h11914 | h11914
                  · rcases h0emin with h11915 | h11915 | h11915 | h11915 | h11915
                    · linarith only [h11915, hlam, p11864_1, u0elo4]
                    · rcases h1bigk with h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c | h11917c
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h0, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h6310, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h9935, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11282, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        rcases p11917_3 (m.d 0 1) (by simp) with h11923 | h11923
                        · linarith only [h11923, hlam, p11917_0]
                        · rcases p11917_3 (m.d 1 2) (by simp) with h11925 | h11925
                          · rcases p11917_3 (m.d 1 3) (by simp) with h11926 | h11926
                            · linarith only [h11850, h11926, hlam]
                            · linarith only [h11926, h6310, hlam]
                          · linarith only [h11925, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11847, h11849, h6310, hc01, hc12, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11849, h9935, hc01, hc12, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        rcases p11917_3 (m.d 0 1) (by simp) with h11934 | h11934
                        · linarith only [h11934, hlam, p11917_0]
                        · rcases p11917_3 (m.d 1 2) (by simp) with h11936 | h11936
                          · rcases p11917_3 (m.d 1 3) (by simp) with h11937 | h11937
                            · rcases p11917_3 (m.d 1 4) (by simp) with h11938 | h11938
                              · linarith only [h11853, h11938, hlam]
                              · linarith only [h11938, h9935, hlam]
                            · linarith only [h11937, hlam, p11917_0]
                          · linarith only [h0, h11936, hlam]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11850, hlam, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        rcases p11917_3 (m.d 0 1) (by simp) with h11947 | h11947
                        · linarith only [h11947, hlam, p11917_0]
                        · rcases p11917_3 (m.d 1 2) (by simp) with h11949 | h11949
                          · rcases p11917_3 (m.d 1 3) (by simp) with h11950 | h11950
                            · rcases p11917_3 (m.d 1 4) (by simp) with h11951 | h11951
                              · rcases p11917_3 (m.d 1 5) (by simp) with h11952 | h11952
                                · linarith only [h11855, h11952, hlam]
                                · linarith only [h11282, h11952, hlam]
                              · linarith only [h11951, hlam, p11917_0]
                            · linarith only [h11950, h6310, hlam]
                          · linarith only [h0, h11949, hlam]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11851, hlam, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11853, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p11864_1, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        rcases p11917_3 (m.d 0 1) (by simp) with h11962 | h11962
                        · linarith only [h11962, hlam, p11917_0]
                        · rcases p11917_3 (m.d 1 2) (by simp) with h11964 | h11964
                          · rcases p11917_3 (m.d 1 3) (by simp) with h11965 | h11965
                            · rcases p11917_3 (m.d 1 4) (by simp) with h11966 | h11966
                              · rcases p11917_3 (m.d 1 5) (by simp) with h11967 | h11967
                                · rcases h3bigk with h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c | h11968c
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h6310, hlam, p11968_1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11844, h11857, h11862, hc34, hlam, hphi, ht0b, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 3) (by simp) with h11972 | h11972
                                    · rcases p11968_3 (m.d 1 3) (by simp) with h11973 | h11973
                                      · rcases p11968_3 (m.d 2 3) (by simp) with h11974 | h11974
                                        · linarith only [h11844, h11974, hlam]
                                        · linarith only [h11856, h11974, hlam]
                                      · linarith only [h11853, h11973, hlam]
                                    · linarith only [h11972, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 3) (by simp) with h11979 | h11979
                                    · rcases p11968_3 (m.d 1 3) (by simp) with h11980 | h11980
                                      · rcases p11968_3 (m.d 2 3) (by simp) with h11981 | h11981
                                        · linarith only [h11844, h11981, hlam]
                                        · linarith only [h11857, h11981, hlam]
                                      · linarith only [h11854, h11980, hlam]
                                    · linarith only [h11979, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p11864_1, p11968_1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 3) (by simp) with h11988 | h11988
                                    · linarith only [h11988, h6310, hlam]
                                    · linarith only [h11844, h11988, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 3) (by simp) with h11991 | h11991
                                    · linarith only [h11991, h6310, hlam]
                                    · linarith only [h11847, h11991, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    rcases p11968_3 (m.d 0 3) (by simp) with h11994 | h11994
                                    · linarith only [h11994, h6310, hlam]
                                    · linarith only [h11848, h11994, hlam]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11844, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11850, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11844, h11862, hc34, hlam, hphi, ht0b, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11847, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11853, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11856, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11862, hlam, p11968_1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11848, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11854, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11857, hlam, p11968_0]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [h11844, h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p11968_1, u0elo1]
                                  · have p11968_0 := h11968c.1
                                    have p11968_1 := h11968c.2.1
                                    have p11968_2 := h11968c.2.2.1
                                    have p11968_3 := h11968c.2.2.2
                                    linarith only [hlam, p11968_0]
                                · linarith only [h11967, hlam, p11917_0]
                              · linarith only [h11966, h9935, hlam]
                            · linarith only [h11965, h6310, hlam]
                          · linarith only [h0, h11964, hlam]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11852, hlam, p11917_1]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11854, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [h11855, hlam, p11917_0]
                      · have p11917_0 := h11917c.1
                        have p11917_1 := h11917c.2.1
                        have p11917_2 := h11917c.2.2.1
                        have p11917_3 := h11917c.2.2.2
                        linarith only [hlam, p11917_0]
                    · rcases h1bigk with h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c | h12020c
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h0, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h6310, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h9935, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11282, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        rcases p12020_3 (m.d 0 1) (by simp) with h12026 | h12026
                        · linarith only [h12026, hlam, p12020_0]
                        · rcases p12020_3 (m.d 1 2) (by simp) with h12028 | h12028
                          · rcases p12020_3 (m.d 1 3) (by simp) with h12029 | h12029
                            · linarith only [h11850, h12029, hlam]
                            · linarith only [h12029, h6310, hlam]
                          · linarith only [h12028, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p11864_1, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        rcases p12020_3 (m.d 0 1) (by simp) with h12037 | h12037
                        · linarith only [h12037, hlam, p12020_0]
                        · rcases p12020_3 (m.d 1 2) (by simp) with h12039 | h12039
                          · rcases p12020_3 (m.d 1 3) (by simp) with h12040 | h12040
                            · rcases p12020_3 (m.d 1 4) (by simp) with h12041 | h12041
                              · linarith only [h11853, h12041, hlam]
                              · linarith only [h12041, h9935, hlam]
                            · linarith only [h12040, hlam, p12020_0]
                          · linarith only [h0, h12039, hlam]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11850, hlam, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p11864_1, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p11864_1, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        rcases p12020_3 (m.d 0 1) (by simp) with h12050 | h12050
                        · linarith only [h12050, hlam, p12020_0]
                        · rcases p12020_3 (m.d 1 2) (by simp) with h12052 | h12052
                          · rcases p12020_3 (m.d 1 3) (by simp) with h12053 | h12053
                            · rcases p12020_3 (m.d 1 4) (by simp) with h12054 | h12054
                              · rcases p12020_3 (m.d 1 5) (by simp) with h12055 | h12055
                                · linarith only [h11855, h12055, hlam]
                                · linarith only [h11282, h12055, hlam]
                              · linarith only [h12054, hlam, p12020_0]
                            · linarith only [h12053, h6310, hlam]
                          · linarith only [h0, h12052, hlam]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11851, hlam, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11853, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p11864_1, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        rcases p12020_3 (m.d 0 1) (by simp) with h12065 | h12065
                        · linarith only [h12065, hlam, p12020_0]
                        · rcases p12020_3 (m.d 1 2) (by simp) with h12067 | h12067
                          · rcases p12020_3 (m.d 1 3) (by simp) with h12068 | h12068
                            · rcases p12020_3 (m.d 1 4) (by simp) with h12069 | h12069
                              · rcases p12020_3 (m.d 1 5) (by simp) with h12070 | h12070
                                · rcases h3bigk with h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c | h12071c
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h6310, hlam, p12071_1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11844, h11857, hc35, hlam, hphi, ht0b, ht5b, p12071_1, u0elo1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    rcases p12071_3 (m.d 0 3) (by simp) with h12075 | h12075
                                    · rcases p12071_3 (m.d 1 3) (by simp) with h12076 | h12076
                                      · rcases p12071_3 (m.d 2 3) (by simp) with h12077 | h12077
                                        · linarith only [h11844, h12077, hlam]
                                        · linarith only [h11856, h12077, hlam]
                                      · linarith only [h11853, h12076, hlam]
                                    · linarith only [h12075, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    rcases p12071_3 (m.d 0 3) (by simp) with h12082 | h12082
                                    · rcases p12071_3 (m.d 1 3) (by simp) with h12083 | h12083
                                      · rcases p12071_3 (m.d 2 3) (by simp) with h12084 | h12084
                                        · linarith only [h11844, h12084, hlam]
                                        · linarith only [h11857, h12084, hlam]
                                      · linarith only [h11854, h12083, hlam]
                                    · linarith only [h12082, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p11864_1, p12071_1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    rcases p12071_3 (m.d 0 3) (by simp) with h12091 | h12091
                                    · linarith only [h12091, h6310, hlam]
                                    · linarith only [h11844, h12091, hlam]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    rcases p12071_3 (m.d 0 3) (by simp) with h12094 | h12094
                                    · linarith only [h12094, h6310, hlam]
                                    · linarith only [h11847, h12094, hlam]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    rcases p12071_3 (m.d 0 3) (by simp) with h12097 | h12097
                                    · linarith only [h12097, h6310, hlam]
                                    · linarith only [h11848, h12097, hlam]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11844, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11850, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p12071_1, u0elo1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11844, h11862, hc34, hlam, hphi, ht0b, ht45, ht5b, p12071_1, u0elo1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11847, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11853, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11856, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11862, hlam, p12071_1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11848, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11854, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11857, hlam, p12071_0]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [h11844, h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p12071_1, u0elo1]
                                  · have p12071_0 := h12071c.1
                                    have p12071_1 := h12071c.2.1
                                    have p12071_2 := h12071c.2.2.1
                                    have p12071_3 := h12071c.2.2.2
                                    linarith only [hlam, p12071_0]
                                · linarith only [h12070, hlam, p12020_0]
                              · linarith only [h12069, h9935, hlam]
                            · linarith only [h12068, h6310, hlam]
                          · linarith only [h0, h12067, hlam]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11852, hlam, p12020_1]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11854, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [h11855, hlam, p12020_0]
                      · have p12020_0 := h12020c.1
                        have p12020_1 := h12020c.2.1
                        have p12020_2 := h12020c.2.2.1
                        have p12020_3 := h12020c.2.2.2
                        linarith only [hlam, p12020_0]
                    · rcases h1bigk with h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c | h12123c
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h0, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h6310, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h9935, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11282, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        rcases p12123_3 (m.d 0 1) (by simp) with h12129 | h12129
                        · linarith only [h12129, hlam, p12123_0]
                        · rcases p12123_3 (m.d 1 2) (by simp) with h12131 | h12131
                          · rcases p12123_3 (m.d 1 3) (by simp) with h12132 | h12132
                            · linarith only [h11850, h12132, hlam]
                            · linarith only [h12132, h6310, hlam]
                          · linarith only [h12131, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h9935, hc01, hc12, hlam, hphi, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p11864_1, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        rcases p12123_3 (m.d 0 1) (by simp) with h12140 | h12140
                        · linarith only [h12140, hlam, p12123_0]
                        · rcases p12123_3 (m.d 1 2) (by simp) with h12142 | h12142
                          · rcases p12123_3 (m.d 1 3) (by simp) with h12143 | h12143
                            · rcases p12123_3 (m.d 1 4) (by simp) with h12144 | h12144
                              · linarith only [h11853, h12144, hlam]
                              · linarith only [h12144, h9935, hlam]
                            · linarith only [h12143, hlam, p12123_0]
                          · linarith only [h0, h12142, hlam]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11850, hlam, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p11864_1, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p11864_1, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        rcases p12123_3 (m.d 0 1) (by simp) with h12153 | h12153
                        · linarith only [h12153, hlam, p12123_0]
                        · rcases p12123_3 (m.d 1 2) (by simp) with h12155 | h12155
                          · rcases p12123_3 (m.d 1 3) (by simp) with h12156 | h12156
                            · rcases p12123_3 (m.d 1 4) (by simp) with h12157 | h12157
                              · rcases p12123_3 (m.d 1 5) (by simp) with h12158 | h12158
                                · linarith only [h11855, h12158, hlam]
                                · linarith only [h11282, h12158, hlam]
                              · linarith only [h12157, hlam, p12123_0]
                            · linarith only [h12156, h6310, hlam]
                          · linarith only [h0, h12155, hlam]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11851, hlam, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11853, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p11864_1, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        rcases p12123_3 (m.d 0 1) (by simp) with h12168 | h12168
                        · linarith only [h12168, hlam, p12123_0]
                        · rcases p12123_3 (m.d 1 2) (by simp) with h12170 | h12170
                          · rcases p12123_3 (m.d 1 3) (by simp) with h12171 | h12171
                            · rcases p12123_3 (m.d 1 4) (by simp) with h12172 | h12172
                              · rcases p12123_3 (m.d 1 5) (by simp) with h12173 | h12173
                                · rcases h3bigk with h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c | h12174c
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h6310, hlam, p12174_1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11844, h11857, hc35, hlam, hphi, ht0b, ht5b, p12174_1, u0elo1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    rcases p12174_3 (m.d 0 3) (by simp) with h12178 | h12178
                                    · rcases p12174_3 (m.d 1 3) (by simp) with h12179 | h12179
                                      · rcases p12174_3 (m.d 2 3) (by simp) with h12180 | h12180
                                        · linarith only [h11844, h12180, hlam]
                                        · linarith only [h11856, h12180, hlam]
                                      · linarith only [h11853, h12179, hlam]
                                    · linarith only [h12178, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    rcases p12174_3 (m.d 0 3) (by simp) with h12185 | h12185
                                    · rcases p12174_3 (m.d 1 3) (by simp) with h12186 | h12186
                                      · rcases p12174_3 (m.d 2 3) (by simp) with h12187 | h12187
                                        · linarith only [h11844, h12187, hlam]
                                        · linarith only [h11857, h12187, hlam]
                                      · linarith only [h11854, h12186, hlam]
                                    · linarith only [h12185, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p11864_1, p12174_1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    rcases p12174_3 (m.d 0 3) (by simp) with h12194 | h12194
                                    · linarith only [h12194, h6310, hlam]
                                    · linarith only [h11844, h12194, hlam]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    rcases p12174_3 (m.d 0 3) (by simp) with h12197 | h12197
                                    · linarith only [h12197, h6310, hlam]
                                    · linarith only [h11847, h12197, hlam]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    rcases p12174_3 (m.d 0 3) (by simp) with h12200 | h12200
                                    · linarith only [h12200, h6310, hlam]
                                    · linarith only [h11848, h12200, hlam]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11844, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11850, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p12174_1, u0elo1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11844, h11862, hc34, hlam, hphi, ht0b, ht45, ht5b, p12174_1, u0elo1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11847, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11853, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11856, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11862, hlam, p12174_1]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11848, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11854, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11857, hlam, p12174_0]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p12174_1, u0elo2]
                                  · have p12174_0 := h12174c.1
                                    have p12174_1 := h12174c.2.1
                                    have p12174_2 := h12174c.2.2.1
                                    have p12174_3 := h12174c.2.2.2
                                    linarith only [hlam, p12174_0]
                                · linarith only [h12173, hlam, p12123_0]
                              · linarith only [h12172, h9935, hlam]
                            · linarith only [h12171, h6310, hlam]
                          · linarith only [h0, h12170, hlam]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11852, hlam, p12123_1]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11854, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [h11855, hlam, p12123_0]
                      · have p12123_0 := h12123c.1
                        have p12123_1 := h12123c.2.1
                        have p12123_2 := h12123c.2.2.1
                        have p12123_3 := h12123c.2.2.2
                        linarith only [hlam, p12123_0]
                    · rcases h1bigk with h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c | h12226c
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h0, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h6310, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h9935, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11282, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        rcases p12226_3 (m.d 0 1) (by simp) with h12232 | h12232
                        · linarith only [h12232, hlam, p12226_0]
                        · rcases p12226_3 (m.d 1 2) (by simp) with h12234 | h12234
                          · rcases p12226_3 (m.d 1 3) (by simp) with h12235 | h12235
                            · linarith only [h11850, h12235, hlam]
                            · linarith only [h12235, h6310, hlam]
                          · linarith only [h12234, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h6310, hc01, hc12, hlam, hphi, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11849, h9935, hc01, hc12, hlam, hphi, p11864_1, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11282, hc01, hc12, hlam, hphi, p11864_1, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        rcases p12226_3 (m.d 0 1) (by simp) with h12243 | h12243
                        · linarith only [h12243, hlam, p12226_0]
                        · rcases p12226_3 (m.d 1 2) (by simp) with h12245 | h12245
                          · rcases p12226_3 (m.d 1 3) (by simp) with h12246 | h12246
                            · rcases p12226_3 (m.d 1 4) (by simp) with h12247 | h12247
                              · linarith only [h11853, h12247, hlam]
                              · linarith only [h12247, h9935, hlam]
                            · linarith only [h12246, hlam, p12226_0]
                          · linarith only [h0, h12245, hlam]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11850, hlam, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11849, h9935, hc01, hc13, hlam, hphi, p11864_1, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11282, h11850, hc01, hc12, hlam, hphi, p11864_1, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        rcases p12226_3 (m.d 0 1) (by simp) with h12256 | h12256
                        · linarith only [h12256, hlam, p12226_0]
                        · rcases p12226_3 (m.d 1 2) (by simp) with h12258 | h12258
                          · rcases p12226_3 (m.d 1 3) (by simp) with h12259 | h12259
                            · rcases p12226_3 (m.d 1 4) (by simp) with h12260 | h12260
                              · rcases p12226_3 (m.d 1 5) (by simp) with h12261 | h12261
                                · linarith only [h11855, h12261, hlam]
                                · linarith only [h11282, h12261, hlam]
                              · linarith only [h12260, hlam, p12226_0]
                            · linarith only [h12259, h6310, hlam]
                          · linarith only [h0, h12258, hlam]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11851, hlam, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11853, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11282, hc01, hc14, hlam, hphi, p11864_1, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        rcases p12226_3 (m.d 0 1) (by simp) with h12271 | h12271
                        · linarith only [h12271, hlam, p12226_0]
                        · rcases p12226_3 (m.d 1 2) (by simp) with h12273 | h12273
                          · rcases p12226_3 (m.d 1 3) (by simp) with h12274 | h12274
                            · rcases p12226_3 (m.d 1 4) (by simp) with h12275 | h12275
                              · rcases p12226_3 (m.d 1 5) (by simp) with h12276 | h12276
                                · rcases h3bigk with h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c | h12277c
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h6310, hlam, p12277_1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11844, h11857, hc35, hlam, hphi, ht0b, ht5b, p12277_1, u0elo1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    rcases p12277_3 (m.d 0 3) (by simp) with h12281 | h12281
                                    · rcases p12277_3 (m.d 1 3) (by simp) with h12282 | h12282
                                      · rcases p12277_3 (m.d 2 3) (by simp) with h12283 | h12283
                                        · linarith only [h11844, h12283, hlam]
                                        · linarith only [h11856, h12283, hlam]
                                      · linarith only [h11853, h12282, hlam]
                                    · linarith only [h12281, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    rcases p12277_3 (m.d 0 3) (by simp) with h12288 | h12288
                                    · rcases p12277_3 (m.d 1 3) (by simp) with h12289 | h12289
                                      · rcases p12277_3 (m.d 2 3) (by simp) with h12290 | h12290
                                        · linarith only [h11844, h12290, hlam]
                                        · linarith only [h11857, h12290, hlam]
                                      · linarith only [h11854, h12289, hlam]
                                    · linarith only [h12288, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11847, h11849, h11850, hc01, hc12, hlam, hphi, p11864_1, p12277_1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    rcases p12277_3 (m.d 0 3) (by simp) with h12297 | h12297
                                    · linarith only [h12297, h6310, hlam]
                                    · linarith only [h11844, h12297, hlam]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    rcases p12277_3 (m.d 0 3) (by simp) with h12300 | h12300
                                    · linarith only [h12300, h6310, hlam]
                                    · linarith only [h11847, h12300, hlam]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    rcases p12277_3 (m.d 0 3) (by simp) with h12303 | h12303
                                    · linarith only [h12303, h6310, hlam]
                                    · linarith only [h11848, h12303, hlam]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11844, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11850, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p12277_1, u0elo1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11844, h11862, hc34, hlam, hphi, ht0b, ht45, ht5b, p12277_1, u0elo1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11847, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11853, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11856, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11862, hlam, p12277_1]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11848, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11854, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11857, hlam, p12277_0]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p12277_1, u0elo2]
                                  · have p12277_0 := h12277c.1
                                    have p12277_1 := h12277c.2.1
                                    have p12277_2 := h12277c.2.2.1
                                    have p12277_3 := h12277c.2.2.2
                                    linarith only [hlam, p12277_0]
                                · linarith only [h12276, hlam, p12226_0]
                              · linarith only [h12275, h9935, hlam]
                            · linarith only [h12274, h6310, hlam]
                          · linarith only [h0, h12273, hlam]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11852, hlam, p12226_1]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11854, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [h11855, hlam, p12226_0]
                      · have p12226_0 := h12226c.1
                        have p12226_1 := h12226c.2.1
                        have p12226_2 := h12226c.2.2.1
                        have p12226_3 := h12226c.2.2.2
                        linarith only [hlam, p12226_0]
                  · linarith only [h11282, h11914, hlam]
                · linarith only [h11913, h9935, hlam]
              · linarith only [h11912, h6310, hlam]
            · linarith only [h0, h11911, hlam]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11846, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11848, hlam, p11864_0]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [h11849, hlam, p11864_1]
        · have p11864_0 := h11864c.1
          have p11864_1 := h11864c.2.1
          have p11864_2 := h11864c.2.2.1
          have p11864_3 := h11864c.2.2.2
          linarith only [hlam, p11864_0]
  · linarith only [h11844, h11848, h11856, h11857, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]

end R2N4
