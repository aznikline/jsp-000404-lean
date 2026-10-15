import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x1_x1_x0 (m : N7Model)
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
    (h11847 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13714 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h13836 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h13837 | h13837
  · rcases m.htr 1 2 4 (by decide) (by decide) with h13838 | h13838
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13839 | h13839
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13840 | h13840
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13841 | h13841
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13842 | h13842
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13843 | h13843
              · linarith only [h11844, h11847, h13843, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13845 | h13845
                · linarith only [h11844, h13714, h13845, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13847 | h13847
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13848 | h13848
                    · rcases h0bigk with h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c | h13849c
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h0, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h6310, hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h9935, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11282, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        rcases p13849_3 (m.d 0 1) (by simp) with h13855 | h13855
                        · linarith only [h0, h13855, hlam]
                        · rcases p13849_3 (m.d 0 2) (by simp) with h13857 | h13857
                          · rcases p13849_3 (m.d 0 3) (by simp) with h13858 | h13858
                            · linarith only [h11844, h13858, hlam]
                            · linarith only [h13858, h6310, hlam]
                          · linarith only [h0, h13857, hlam]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        rcases p13849_3 (m.d 0 1) (by simp) with h13863 | h13863
                        · linarith only [h0, h13863, hlam]
                        · rcases p13849_3 (m.d 0 2) (by simp) with h13865 | h13865
                          · rcases p13849_3 (m.d 0 3) (by simp) with h13866 | h13866
                            · linarith only [h11844, h13866, hlam]
                            · rcases p13849_3 (m.d 0 4) (by simp) with h13868 | h13868
                              · linarith only [h11845, h13868, hlam]
                              · linarith only [h11847, h13868, hlam]
                          · linarith only [h11844, h13865, hlam]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11845, h13847, hc45, hlam, hphi, ht0b, ht5b, p13849_1, u0elo1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        rcases p13849_3 (m.d 0 1) (by simp) with h13873 | h13873
                        · linarith only [h0, h13873, hlam]
                        · rcases p13849_3 (m.d 0 2) (by simp) with h13875 | h13875
                          · rcases p13849_3 (m.d 0 3) (by simp) with h13876 | h13876
                            · linarith only [h11844, h13876, hlam]
                            · rcases p13849_3 (m.d 0 4) (by simp) with h13878 | h13878
                              · linarith only [h11845, h13878, hlam]
                              · linarith only [h13836, h13878, hlam]
                          · linarith only [h11846, h13875, hlam]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h13714, h13837, h13840, h13848, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11844, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11847, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h13714, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11847, h13837, h13840, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11845, hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11847, h13837, h13840, h6310, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [hlam, p13849_0]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11282, h11847, h13837, h13840, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h13714, h13837, h13840, h13848, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h11846, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h13714, h13837, h13840, h13848, h6310, hc01, hc12, hlam, hphi, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [h13836, hlam, p13849_1]
                      · have p13849_0 := h13849c.1
                        have p13849_1 := h13849c.2.1
                        have p13849_2 := h13849c.2.2.1
                        have p13849_3 := h13849c.2.2.2
                        linarith only [hlam, p13849_0]
                    · linarith only [h11847, h13836, h13848, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13898 | h13898
                    · rcases h0bigk with h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c | h13899c
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h0, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h6310, hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h9935, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11282, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        rcases p13899_3 (m.d 0 1) (by simp) with h13905 | h13905
                        · linarith only [h0, h13905, hlam]
                        · rcases p13899_3 (m.d 0 2) (by simp) with h13907 | h13907
                          · rcases p13899_3 (m.d 0 3) (by simp) with h13908 | h13908
                            · linarith only [h11844, h13908, hlam]
                            · linarith only [h13908, h6310, hlam]
                          · linarith only [h0, h13907, hlam]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        rcases p13899_3 (m.d 0 1) (by simp) with h13913 | h13913
                        · linarith only [h0, h13913, hlam]
                        · rcases p13899_3 (m.d 0 2) (by simp) with h13915 | h13915
                          · rcases p13899_3 (m.d 0 3) (by simp) with h13916 | h13916
                            · linarith only [h11844, h13916, hlam]
                            · rcases p13899_3 (m.d 0 4) (by simp) with h13918 | h13918
                              · linarith only [h11845, h13918, hlam]
                              · linarith only [h11847, h13918, hlam]
                          · linarith only [h11844, h13915, hlam]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h13836, h13843, h13847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13899_1, u0elo1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h13836, h13843, h13847, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13899_1, u0elo1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, h13714, h13836, h13837, h13840, h13843, h13847, hc01, hc12, hc23, hc35, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11844, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h13714, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, h13837, h13840, hc01, hc12, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11845, hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, h13837, h13840, h6310, hc01, hc12, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [hlam, p13899_0]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11282, h11847, h13837, h13840, hc01, hc12, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, h13836, h13837, h13840, hc01, hc12, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11846, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h11847, h13836, h13837, h13840, h6310, hc01, hc12, hlam, hphi, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [h13836, hlam, p13899_1]
                      · have p13899_0 := h13899c.1
                        have p13899_1 := h13899c.2.1
                        have p13899_2 := h13899c.2.2.1
                        have p13899_3 := h13899c.2.2.2
                        linarith only [hlam, p13899_0]
                    · linarith only [h11847, h13836, h13898, hlam]
            · linarith only [h11847, h13836, h13837, h13840, h13842, h9935, hc01, hc12, hlam, hphi]
          · linarith only [h11847, h13840, h13841, h6310, hc01, hc35, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13942 | h13942
          · linarith only [h13714, h13840, h13942, h6310, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13944 | h13944
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13945 | h13945
              · linarith only [h13840, h13945, h6310, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13947 | h13947
                · linarith only [h13942, h13947, h6310, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13949 | h13949
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13950 | h13950
                    · rcases h0bigk with h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c | h13951c
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h0, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h6310, hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h9935, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h11282, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h13957 | h13957
                        · linarith only [h0, h13957, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h13959 | h13959
                          · rcases p13951_3 (m.d 0 3) (by simp) with h13960 | h13960
                            · linarith only [h11844, h13960, hlam]
                            · linarith only [h13960, h6310, hlam]
                          · linarith only [h0, h13959, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h13965 | h13965
                        · linarith only [h0, h13965, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h13967 | h13967
                          · rcases p13951_3 (m.d 0 3) (by simp) with h13968 | h13968
                            · linarith only [h11844, h13968, hlam]
                            · rcases p13951_3 (m.d 0 4) (by simp) with h13970 | h13970
                              · linarith only [h11845, h13970, hlam]
                              · linarith only [h11847, h13970, hlam]
                          · linarith only [h11844, h13967, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h13836, hc45, hlam, hphi, ht0b, ht5b, p13951_1, u0elo1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h13975 | h13975
                        · linarith only [h0, h13975, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h13977 | h13977
                          · rcases p13951_3 (m.d 0 3) (by simp) with h13978 | h13978
                            · linarith only [h11844, h13978, hlam]
                            · rcases p13951_3 (m.d 0 4) (by simp) with h13980 | h13980
                              · linarith only [h11845, h13980, hlam]
                              · linarith only [h13836, h13980, hlam]
                          · linarith only [h11846, h13977, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h13942, h13950, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h11844, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h11847, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h13714, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h13989 | h13989
                        · linarith only [h13989, h9935, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h13991 | h13991
                          · rcases p13951_3 (m.d 0 3) (by simp) with h13992 | h13992
                            · linarith only [h11847, h13992, hlam]
                            · linarith only [h13992, h6310, hlam]
                          · linarith only [h0, h13991, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h11845, hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h13997 | h13997
                        · linarith only [h13997, h9935, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h13999 | h13999
                          · rcases p13951_3 (m.d 0 3) (by simp) with h14000 | h14000
                            · linarith only [h11847, h14000, hlam]
                            · rcases p13951_3 (m.d 0 4) (by simp) with h14002 | h14002
                              · rcases p13951_3 (m.d 0 5) (by simp) with h14003 | h14003
                                · linarith only [h13836, h14003, hlam]
                                · linarith only [h13714, h14003, hlam]
                              · linarith only [h11847, h14002, hlam]
                          · linarith only [h11844, h13999, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [hlam, p13951_0]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h14009 | h14009
                        · linarith only [h14009, h9935, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h14011 | h14011
                          · rcases p13951_3 (m.d 0 3) (by simp) with h14012 | h14012
                            · linarith only [h11847, h14012, hlam]
                            · rcases p13951_3 (m.d 0 4) (by simp) with h14014 | h14014
                              · rcases p13951_3 (m.d 0 5) (by simp) with h14015 | h14015
                                · linarith only [h13836, h14015, hlam]
                                · rcases h0emin with h14017 | h14017 | h14017 | h14017 | h14017
                                  · linarith only [h13714, h14017, h6310, hlam, p13951_1, u0elo3]
                                  · rcases h1bigk with h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c | h14019c
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h0, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h6310, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h9935, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h11282, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      rcases p14019_3 (m.d 0 1) (by simp) with h14025 | h14025
                                      · linarith only [h14025, hlam, p14019_0]
                                      · rcases p14019_3 (m.d 1 2) (by simp) with h14027 | h14027
                                        · rcases p14019_3 (m.d 1 3) (by simp) with h14028 | h14028
                                          · linarith only [h13837, h14028, hlam]
                                          · linarith only [h14028, h6310, hlam]
                                        · linarith only [h14027, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13714, h6310, h9935, hc01, hc12, hlam, hphi, p13951_1, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13942, h6310, hc01, hc12, hlam, hphi, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13837, hlam, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13840, hlam, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13942, hlam, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      rcases p14019_3 (m.d 0 1) (by simp) with h14041 | h14041
                                      · linarith only [h14041, hlam, p14019_0]
                                      · rcases p14019_3 (m.d 1 2) (by simp) with h14043 | h14043
                                        · rcases p14019_3 (m.d 1 3) (by simp) with h14044 | h14044
                                          · linarith only [h13840, h14044, hlam]
                                          · linarith only [h14044, h6310, hlam]
                                        · linarith only [h0, h14043, hlam]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13838, hlam, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13840, h13942, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      rcases p14019_3 (m.d 0 1) (by simp) with h14052 | h14052
                                      · linarith only [h14052, hlam, p14019_0]
                                      · rcases p14019_3 (m.d 1 2) (by simp) with h14054 | h14054
                                        · rcases p14019_3 (m.d 1 3) (by simp) with h14055 | h14055
                                          · linarith only [h13942, h14055, hlam]
                                          · linarith only [h14055, h6310, hlam]
                                        · linarith only [h0, h14054, hlam]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13839, hlam, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14019_1]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [h13944, hlam, p14019_0]
                                    · have p14019_0 := h14019c.1
                                      have p14019_1 := h14019c.2.1
                                      have p14019_2 := h14019c.2.2.1
                                      have p14019_3 := h14019c.2.2.2
                                      linarith only [hlam, p14019_0]
                                  · linarith only [h11845, h13714, h14017, hlam, p13951_1, u0elo1]
                                  · rcases h1bigk with h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c | h14064c
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h0, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h6310, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h9935, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h11282, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      rcases p14064_3 (m.d 0 1) (by simp) with h14070 | h14070
                                      · linarith only [h14070, hlam, p14064_0]
                                      · rcases p14064_3 (m.d 1 2) (by simp) with h14072 | h14072
                                        · rcases p14064_3 (m.d 1 3) (by simp) with h14073 | h14073
                                          · linarith only [h13837, h14073, hlam]
                                          · linarith only [h14073, h6310, hlam]
                                        · linarith only [h14072, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13837, hlam, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13840, hlam, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13942, hlam, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      rcases p14064_3 (m.d 0 1) (by simp) with h14086 | h14086
                                      · linarith only [h14086, hlam, p14064_0]
                                      · rcases p14064_3 (m.d 1 2) (by simp) with h14088 | h14088
                                        · rcases p14064_3 (m.d 1 3) (by simp) with h14089 | h14089
                                          · linarith only [h13840, h14089, hlam]
                                          · linarith only [h14089, h6310, hlam]
                                        · linarith only [h0, h14088, hlam]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13838, hlam, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13840, h13942, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      rcases p14064_3 (m.d 0 1) (by simp) with h14097 | h14097
                                      · linarith only [h14097, hlam, p14064_0]
                                      · rcases p14064_3 (m.d 1 2) (by simp) with h14099 | h14099
                                        · rcases p14064_3 (m.d 1 3) (by simp) with h14100 | h14100
                                          · linarith only [h13942, h14100, hlam]
                                          · linarith only [h14100, h6310, hlam]
                                        · linarith only [h0, h14099, hlam]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13839, hlam, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14064_1]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [h13944, hlam, p14064_0]
                                    · have p14064_0 := h14064c.1
                                      have p14064_1 := h14064c.2.1
                                      have p14064_2 := h14064c.2.2.1
                                      have p14064_3 := h14064c.2.2.2
                                      linarith only [hlam, p14064_0]
                                  · linarith only [h11845, h14017, hlam, p13951_1, u0elo1]
                              · linarith only [h13836, h14014, hlam]
                          · linarith only [h11846, h14011, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h14111 | h14111
                        · linarith only [h11282, h14111, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h14113 | h14113
                          · rcases p13951_3 (m.d 0 3) (by simp) with h14114 | h14114
                            · linarith only [h13714, h14114, hlam]
                            · linarith only [h14114, h6310, hlam]
                          · linarith only [h0, h14113, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h11846, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        rcases p13951_3 (m.d 0 1) (by simp) with h14119 | h14119
                        · linarith only [h11282, h14119, hlam]
                        · rcases p13951_3 (m.d 0 2) (by simp) with h14121 | h14121
                          · rcases p13951_3 (m.d 0 3) (by simp) with h14122 | h14122
                            · linarith only [h13714, h14122, hlam]
                            · rcases p13951_3 (m.d 0 4) (by simp) with h14124 | h14124
                              · rcases p13951_3 (m.d 0 5) (by simp) with h14125 | h14125
                                · rcases h0emin with h14126 | h14126 | h14126 | h14126 | h14126
                                  · linarith only [h14126, h6310, hlam, p13951_1, u0elo4]
                                  · rcases h1bigk with h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c | h14128c
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h0, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h6310, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h9935, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h11282, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      rcases p14128_3 (m.d 0 1) (by simp) with h14134 | h14134
                                      · linarith only [h14134, hlam, p14128_0]
                                      · rcases p14128_3 (m.d 1 2) (by simp) with h14136 | h14136
                                        · rcases p14128_3 (m.d 1 3) (by simp) with h14137 | h14137
                                          · linarith only [h13837, h14137, hlam]
                                          · linarith only [h14137, h6310, hlam]
                                        · linarith only [h14136, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13837, hlam, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13840, hlam, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13942, hlam, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      rcases p14128_3 (m.d 0 1) (by simp) with h14150 | h14150
                                      · linarith only [h14150, hlam, p14128_0]
                                      · rcases p14128_3 (m.d 1 2) (by simp) with h14152 | h14152
                                        · rcases p14128_3 (m.d 1 3) (by simp) with h14153 | h14153
                                          · linarith only [h13840, h14153, hlam]
                                          · linarith only [h14153, h6310, hlam]
                                        · linarith only [h0, h14152, hlam]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13838, hlam, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h11282, h13840, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13951_1, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      rcases p14128_3 (m.d 0 1) (by simp) with h14161 | h14161
                                      · linarith only [h14161, hlam, p14128_0]
                                      · rcases p14128_3 (m.d 1 2) (by simp) with h14163 | h14163
                                        · rcases p14128_3 (m.d 1 3) (by simp) with h14164 | h14164
                                          · linarith only [h13942, h14164, hlam]
                                          · linarith only [h14164, h6310, hlam]
                                        · linarith only [h0, h14163, hlam]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13839, hlam, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14128_1]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [h13944, hlam, p14128_0]
                                    · have p14128_0 := h14128c.1
                                      have p14128_1 := h14128c.2.1
                                      have p14128_2 := h14128c.2.2.1
                                      have p14128_3 := h14128c.2.2.2
                                      linarith only [hlam, p14128_0]
                                  · linarith only [h11845, h13836, h14126, hlam, p13951_1, u0elo1]
                                  · rcases h1bigk with h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c | h14173c
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h0, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h6310, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h9935, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h11282, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      rcases p14173_3 (m.d 0 1) (by simp) with h14179 | h14179
                                      · linarith only [h14179, hlam, p14173_0]
                                      · rcases p14173_3 (m.d 1 2) (by simp) with h14181 | h14181
                                        · rcases p14173_3 (m.d 1 3) (by simp) with h14182 | h14182
                                          · linarith only [h13837, h14182, hlam]
                                          · linarith only [h14182, h6310, hlam]
                                        · linarith only [h14181, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13837, hlam, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13840, hlam, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13942, hlam, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      rcases p14173_3 (m.d 0 1) (by simp) with h14195 | h14195
                                      · linarith only [h14195, hlam, p14173_0]
                                      · rcases p14173_3 (m.d 1 2) (by simp) with h14197 | h14197
                                        · rcases p14173_3 (m.d 1 3) (by simp) with h14198 | h14198
                                          · linarith only [h13840, h14198, hlam]
                                          · linarith only [h14198, h6310, hlam]
                                        · linarith only [h0, h14197, hlam]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13838, hlam, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h11282, h13840, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13951_1, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      rcases p14173_3 (m.d 0 1) (by simp) with h14206 | h14206
                                      · linarith only [h14206, hlam, p14173_0]
                                      · rcases p14173_3 (m.d 1 2) (by simp) with h14208 | h14208
                                        · rcases p14173_3 (m.d 1 3) (by simp) with h14209 | h14209
                                          · linarith only [h13942, h14209, hlam]
                                          · linarith only [h14209, h6310, hlam]
                                        · linarith only [h0, h14208, hlam]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13839, hlam, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14173_1]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [h13944, hlam, p14173_0]
                                    · have p14173_0 := h14173c.1
                                      have p14173_1 := h14173c.2.1
                                      have p14173_2 := h14173c.2.2.1
                                      have p14173_3 := h14173c.2.2.2
                                      linarith only [hlam, p14173_0]
                                  · rcases h1bigk with h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c | h14217c
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h0, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h6310, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h9935, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h11282, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      rcases p14217_3 (m.d 0 1) (by simp) with h14223 | h14223
                                      · linarith only [h14223, hlam, p14217_0]
                                      · rcases p14217_3 (m.d 1 2) (by simp) with h14225 | h14225
                                        · rcases p14217_3 (m.d 1 3) (by simp) with h14226 | h14226
                                          · linarith only [h13837, h14226, hlam]
                                          · linarith only [h14226, h6310, hlam]
                                        · linarith only [h14225, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13837, hlam, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13840, hlam, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13942, hlam, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      rcases p14217_3 (m.d 0 1) (by simp) with h14239 | h14239
                                      · linarith only [h14239, hlam, p14217_0]
                                      · rcases p14217_3 (m.d 1 2) (by simp) with h14241 | h14241
                                        · rcases p14217_3 (m.d 1 3) (by simp) with h14242 | h14242
                                          · linarith only [h13840, h14242, hlam]
                                          · linarith only [h14242, h6310, hlam]
                                        · linarith only [h0, h14241, hlam]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13838, hlam, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h11282, h13840, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p13951_1, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      rcases p14217_3 (m.d 0 1) (by simp) with h14250 | h14250
                                      · linarith only [h14250, hlam, p14217_0]
                                      · rcases p14217_3 (m.d 1 2) (by simp) with h14252 | h14252
                                        · rcases p14217_3 (m.d 1 3) (by simp) with h14253 | h14253
                                          · linarith only [h13942, h14253, hlam]
                                          · linarith only [h14253, h6310, hlam]
                                        · linarith only [h0, h14252, hlam]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13839, hlam, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14217_1]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [h13944, hlam, p14217_0]
                                    · have p14217_0 := h14217c.1
                                      have p14217_1 := h14217c.2.1
                                      have p14217_2 := h14217c.2.2.1
                                      have p14217_3 := h14217c.2.2.2
                                      linarith only [hlam, p14217_0]
                                · linarith only [h13714, h14125, hlam]
                              · linarith only [h11847, h14124, hlam]
                          · linarith only [h11844, h14121, hlam]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [h13836, hlam, p13951_1]
                      · have p13951_0 := h13951c.1
                        have p13951_1 := h13951c.2.1
                        have p13951_2 := h13951c.2.2.1
                        have p13951_3 := h13951c.2.2.2
                        linarith only [hlam, p13951_0]
                    · linarith only [h13840, h13949, h13950, h9935, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14267 | h14267
                    · rcases h0bigk with h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c | h14268c
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h0, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h6310, hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h9935, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11282, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14274 | h14274
                        · linarith only [h0, h14274, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14276 | h14276
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14277 | h14277
                            · linarith only [h11844, h14277, hlam]
                            · linarith only [h14277, h6310, hlam]
                          · linarith only [h0, h14276, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14282 | h14282
                        · linarith only [h0, h14282, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14284 | h14284
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14285 | h14285
                            · linarith only [h11844, h14285, hlam]
                            · rcases p14268_3 (m.d 0 4) (by simp) with h14287 | h14287
                              · linarith only [h11845, h14287, hlam]
                              · linarith only [h11847, h14287, hlam]
                          · linarith only [h11844, h14284, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h13836, h13949, hc24, hlam, hphi, ht0b, ht45, ht5b, p14268_1, u0elo1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h13836, h13949, hc24, hlam, hphi, ht0b, ht45, ht5b, p14268_1, u0elo1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11847, hc01, hc34, hlam, hphi, ht12, ht23, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11844, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11847, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h13714, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14298 | h14298
                        · linarith only [h14298, h9935, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14300 | h14300
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14301 | h14301
                            · linarith only [h11847, h14301, hlam]
                            · linarith only [h14301, h6310, hlam]
                          · linarith only [h0, h14300, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11845, hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14306 | h14306
                        · linarith only [h14306, h9935, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14308 | h14308
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14309 | h14309
                            · linarith only [h11847, h14309, hlam]
                            · rcases p14268_3 (m.d 0 4) (by simp) with h14311 | h14311
                              · rcases p14268_3 (m.d 0 5) (by simp) with h14312 | h14312
                                · linarith only [h13836, h14312, hlam]
                                · linarith only [h13714, h14312, hlam]
                              · linarith only [h11847, h14311, hlam]
                          · linarith only [h11844, h14308, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [hlam, p14268_0]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h13836, h13945, h13949, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14268_1, u0elo3]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14319 | h14319
                        · linarith only [h11282, h14319, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14321 | h14321
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14322 | h14322
                            · linarith only [h13714, h14322, hlam]
                            · linarith only [h14322, h6310, hlam]
                          · linarith only [h0, h14321, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h11846, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        rcases p14268_3 (m.d 0 1) (by simp) with h14327 | h14327
                        · linarith only [h11282, h14327, hlam]
                        · rcases p14268_3 (m.d 0 2) (by simp) with h14329 | h14329
                          · rcases p14268_3 (m.d 0 3) (by simp) with h14330 | h14330
                            · linarith only [h13714, h14330, hlam]
                            · rcases p14268_3 (m.d 0 4) (by simp) with h14332 | h14332
                              · rcases p14268_3 (m.d 0 5) (by simp) with h14333 | h14333
                                · rcases h0emin with h14334 | h14334 | h14334 | h14334 | h14334
                                  · linarith only [h14334, h6310, hlam, p14268_1, u0elo4]
                                  · rcases h1bigk with h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c | h14336c
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h0, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h6310, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h9935, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h11282, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      rcases p14336_3 (m.d 0 1) (by simp) with h14342 | h14342
                                      · linarith only [h14342, hlam, p14336_0]
                                      · rcases p14336_3 (m.d 1 2) (by simp) with h14344 | h14344
                                        · rcases p14336_3 (m.d 1 3) (by simp) with h14345 | h14345
                                          · linarith only [h13837, h14345, hlam]
                                          · linarith only [h14345, h6310, hlam]
                                        · linarith only [h14344, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h11282, h13944, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14268_1, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h11282, h6310, hc01, hc12, hlam, hphi, p14268_1, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13837, hlam, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13840, hlam, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13942, hlam, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      rcases p14336_3 (m.d 0 1) (by simp) with h14358 | h14358
                                      · linarith only [h14358, hlam, p14336_0]
                                      · rcases p14336_3 (m.d 1 2) (by simp) with h14360 | h14360
                                        · rcases p14336_3 (m.d 1 3) (by simp) with h14361 | h14361
                                          · linarith only [h13840, h14361, hlam]
                                          · linarith only [h14361, h6310, hlam]
                                        · linarith only [h0, h14360, hlam]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13838, hlam, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h11282, h13840, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14268_1, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      rcases p14336_3 (m.d 0 1) (by simp) with h14369 | h14369
                                      · linarith only [h14369, hlam, p14336_0]
                                      · rcases p14336_3 (m.d 1 2) (by simp) with h14371 | h14371
                                        · rcases p14336_3 (m.d 1 3) (by simp) with h14372 | h14372
                                          · linarith only [h13942, h14372, hlam]
                                          · linarith only [h14372, h6310, hlam]
                                        · linarith only [h0, h14371, hlam]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13839, hlam, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14336_1]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [h13944, hlam, p14336_0]
                                    · have p14336_0 := h14336c.1
                                      have p14336_1 := h14336c.2.1
                                      have p14336_2 := h14336c.2.2.1
                                      have p14336_3 := h14336c.2.2.2
                                      linarith only [hlam, p14336_0]
                                  · linarith only [h14334, hlam, p14268_1, u0elo4]
                                  · rcases h1bigk with h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c | h14381c
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h0, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h6310, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h9935, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h11282, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      rcases p14381_3 (m.d 0 1) (by simp) with h14387 | h14387
                                      · linarith only [h14387, hlam, p14381_0]
                                      · rcases p14381_3 (m.d 1 2) (by simp) with h14389 | h14389
                                        · rcases p14381_3 (m.d 1 3) (by simp) with h14390 | h14390
                                          · linarith only [h13837, h14390, hlam]
                                          · linarith only [h14390, h6310, hlam]
                                        · linarith only [h14389, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13837, hlam, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13840, hlam, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13942, hlam, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      rcases p14381_3 (m.d 0 1) (by simp) with h14403 | h14403
                                      · linarith only [h14403, hlam, p14381_0]
                                      · rcases p14381_3 (m.d 1 2) (by simp) with h14405 | h14405
                                        · rcases p14381_3 (m.d 1 3) (by simp) with h14406 | h14406
                                          · linarith only [h13840, h14406, hlam]
                                          · linarith only [h14406, h6310, hlam]
                                        · linarith only [h0, h14405, hlam]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13838, hlam, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h11282, h13840, hc03, hc34, hlam, hphi, p14268_1, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      rcases p14381_3 (m.d 0 1) (by simp) with h14414 | h14414
                                      · linarith only [h14414, hlam, p14381_0]
                                      · rcases p14381_3 (m.d 1 2) (by simp) with h14416 | h14416
                                        · rcases p14381_3 (m.d 1 3) (by simp) with h14417 | h14417
                                          · linarith only [h13942, h14417, hlam]
                                          · linarith only [h14417, h6310, hlam]
                                        · linarith only [h0, h14416, hlam]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13839, hlam, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14381_1]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [h13944, hlam, p14381_0]
                                    · have p14381_0 := h14381c.1
                                      have p14381_1 := h14381c.2.1
                                      have p14381_2 := h14381c.2.2.1
                                      have p14381_3 := h14381c.2.2.2
                                      linarith only [hlam, p14381_0]
                                  · rcases h1bigk with h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c | h14425c
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h0, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h6310, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h9935, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h11282, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      rcases p14425_3 (m.d 0 1) (by simp) with h14431 | h14431
                                      · linarith only [h14431, hlam, p14425_0]
                                      · rcases p14425_3 (m.d 1 2) (by simp) with h14433 | h14433
                                        · rcases p14425_3 (m.d 1 3) (by simp) with h14434 | h14434
                                          · linarith only [h13837, h14434, hlam]
                                          · linarith only [h14434, h6310, hlam]
                                        · linarith only [h14433, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13840, hc01, hc34, hlam, hphi, ht12, ht23, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13837, hlam, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13840, hlam, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13942, hlam, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      rcases p14425_3 (m.d 0 1) (by simp) with h14447 | h14447
                                      · linarith only [h14447, hlam, p14425_0]
                                      · rcases p14425_3 (m.d 1 2) (by simp) with h14449 | h14449
                                        · rcases p14425_3 (m.d 1 3) (by simp) with h14450 | h14450
                                          · linarith only [h13840, h14450, hlam]
                                          · linarith only [h14450, h6310, hlam]
                                        · linarith only [h0, h14449, hlam]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13838, hlam, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h6310, hc01, hc14, hlam, hphi, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h11282, h13840, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p14268_1, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      rcases p14425_3 (m.d 0 1) (by simp) with h14458 | h14458
                                      · linarith only [h14458, hlam, p14425_0]
                                      · rcases p14425_3 (m.d 1 2) (by simp) with h14460 | h14460
                                        · rcases p14425_3 (m.d 1 3) (by simp) with h14461 | h14461
                                          · linarith only [h13942, h14461, hlam]
                                          · linarith only [h14461, h6310, hlam]
                                        · linarith only [h0, h14460, hlam]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13839, hlam, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h6310, hc01, hc15, hlam, hphi, p14425_1]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [h13944, hlam, p14425_0]
                                    · have p14425_0 := h14425c.1
                                      have p14425_1 := h14425c.2.1
                                      have p14425_2 := h14425c.2.2.1
                                      have p14425_3 := h14425c.2.2.2
                                      linarith only [hlam, p14425_0]
                                · linarith only [h13714, h14333, hlam]
                              · linarith only [h11847, h14332, hlam]
                          · linarith only [h11844, h14329, hlam]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [h13836, hlam, p14268_1]
                      · have p14268_0 := h14268c.1
                        have p14268_1 := h14268c.2.1
                        have p14268_2 := h14268c.2.2.1
                        have p14268_3 := h14268c.2.2.2
                        linarith only [hlam, p14268_0]
                    · linarith only [h13836, h13840, h14267, h9935, hlam]
            · linarith only [h13836, h13944, h9935, hlam]
      · linarith only [h0, h11846, h13839, hlam]
    · linarith only [h0, h11845, h13838, hlam]
  · linarith only [h0, h11844, h13837, hlam]

end R2N4
