import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3368000 in
set_option maxHeartbeats 3368000 in
theorem r1l7_22_13_15_M_IR_L_R_L_I_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h423 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h860 | h860
  · rcases m.htr 0 2 4 (by decide) (by decide) with h861 | h861
    · rcases m.htr 0 2 5 (by decide) (by decide) with h862 | h862
      · rcases m.htr 0 3 4 (by decide) (by decide) with h863 | h863
        · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
          · rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
            · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
              · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
                · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h870 | h870
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h871 | h871
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h872 | h872
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h874 | h874
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h875 | h875
                                · rcases h2bigk with h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c | h876c
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h0, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h872, h875, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p876_1, u3ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    rcases p876_3 (m.d 0 2) (by simp) with h880 | h880
                                    · rcases p876_3 (m.d 1 2) (by simp) with h881 | h881
                                      · rcases p876_3 (m.d 2 3) (by simp) with h882 | h882
                                        · linarith only [h860, h882, hlam]
                                        · linarith only [h872, h882, hlam]
                                      · linarith only [h867, h881, hlam]
                                    · linarith only [h880, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    rcases p876_3 (m.d 0 2) (by simp) with h887 | h887
                                    · rcases p876_3 (m.d 1 2) (by simp) with h888 | h888
                                      · rcases p876_3 (m.d 2 3) (by simp) with h889 | h889
                                        · linarith only [h860, h889, hlam]
                                        · linarith only [h873, h889, hlam]
                                      · linarith only [h868, h888, hlam]
                                    · linarith only [h887, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h860, h872, h875, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p876_1, u3ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h872, h875, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p876_1, u3ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    rcases p876_3 (m.d 0 2) (by simp) with h897 | h897
                                    · linarith only [h0, h897, hlam]
                                    · linarith only [h861, h897, hlam]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    rcases p876_3 (m.d 0 2) (by simp) with h900 | h900
                                    · linarith only [h0, h900, hlam]
                                    · linarith only [h862, h900, hlam]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h860, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h866, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h860, h874, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p876_1, u2ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h0, h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p876_1, u2ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h861, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h867, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h872, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hc24, hlam, hphi, p876_1, u2ehi4]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h862, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h868, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h873, hlam, p876_0]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [h874, hlam, p876_1]
                                  · have p876_0 := h876c.1
                                    have p876_1 := h876c.2.1
                                    have p876_2 := h876c.2.2.1
                                    have p876_3 := h876c.2.2.2
                                    linarith only [hlam, p876_0]
                                · linarith only [h0, h860, h872, h874, h875, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h919 | h919
                                · linarith only [h874, h919, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h2bigk with h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h0, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h0, h872, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p921_1, u3ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    rcases p921_3 (m.d 0 2) (by simp) with h925 | h925
                                    · rcases p921_3 (m.d 1 2) (by simp) with h926 | h926
                                      · rcases p921_3 (m.d 2 3) (by simp) with h927 | h927
                                        · linarith only [h860, h927, hlam]
                                        · linarith only [h872, h927, hlam]
                                      · linarith only [h867, h926, hlam]
                                    · linarith only [h925, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    rcases p921_3 (m.d 0 2) (by simp) with h932 | h932
                                    · rcases p921_3 (m.d 1 2) (by simp) with h933 | h933
                                      · rcases p921_3 (m.d 2 3) (by simp) with h934 | h934
                                        · linarith only [h860, h934, hlam]
                                        · linarith only [h873, h934, hlam]
                                      · linarith only [h868, h933, hlam]
                                    · linarith only [h932, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h860, h873, h919, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p921_1, u3ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h873, h919, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p921_1, u3ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    rcases p921_3 (m.d 0 2) (by simp) with h942 | h942
                                    · linarith only [h0, h942, hlam]
                                    · linarith only [h861, h942, hlam]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    rcases p921_3 (m.d 0 2) (by simp) with h945 | h945
                                    · linarith only [h0, h945, hlam]
                                    · linarith only [h862, h945, hlam]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h860, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h866, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hc23, hlam, hphi, p921_1, u2ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h0, h860, h874, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p921_1, u2ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h861, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h867, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h872, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h874, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h862, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h868, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [h873, hlam, p921_0]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hc25, hlam, hphi, p921_1, u2ehi3]
                                  · have p921_0 := h921c.1
                                    have p921_1 := h921c.2.1
                                    have p921_2 := h921c.2.2.1
                                    have p921_3 := h921c.2.2.2
                                    linarith only [hlam, p921_0]
                            · linarith only [h0, h860, h864, h872, h873, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
                            · linarith only [h872, h964, hc34, hlam, hphi, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h966 | h966
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                                · rcases h2bigk with h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h0, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h971 | h971
                                    · rcases p968_3 (m.d 1 2) (by simp) with h972 | h972
                                      · rcases p968_3 (m.d 2 3) (by simp) with h973 | h973
                                        · linarith only [h973, hlam, p968_0]
                                        · rcases p968_3 (m.d 2 4) (by simp) with h975 | h975
                                          · linarith only [h861, h975, hlam]
                                          · linarith only [h872, h975, hlam]
                                      · linarith only [h866, h972, hlam]
                                    · linarith only [h971, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h980 | h980
                                    · rcases p968_3 (m.d 1 2) (by simp) with h981 | h981
                                      · rcases p968_3 (m.d 2 3) (by simp) with h982 | h982
                                        · linarith only [h860, h982, hlam]
                                        · rcases p968_3 (m.d 2 4) (by simp) with h984 | h984
                                          · linarith only [h984, hlam, p968_0]
                                          · rcases p968_3 (m.d 2 5) (by simp) with h986 | h986
                                            · linarith only [h862, h986, hlam]
                                            · rcases h5bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hlam, p988_0]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h423, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                rcases p988_3 (m.d 0 5) (by simp) with h991 | h991
                                                · rcases p988_3 (m.d 1 5) (by simp) with h992 | h992
                                                  · rcases p988_3 (m.d 2 5) (by simp) with h993 | h993
                                                    · linarith only [h862, h993, hlam]
                                                    · rcases p988_3 (m.d 3 5) (by simp) with h995 | h995
                                                      · linarith only [h864, h995, hlam]
                                                      · linarith only [h964, h995, hlam]
                                                  · linarith only [h868, h992, hlam]
                                                · linarith only [h862, h991, hlam]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h865, h964, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi2]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                rcases p988_3 (m.d 0 5) (by simp) with h1001 | h1001
                                                · rcases p988_3 (m.d 1 5) (by simp) with h1002 | h1002
                                                  · rcases p988_3 (m.d 2 5) (by simp) with h1003 | h1003
                                                    · linarith only [h1003, h862, hlam]
                                                    · linarith only [h1003, h966, hlam]
                                                  · linarith only [h1002, h871, hlam]
                                                · linarith only [h1001, h865, hlam]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h864, h866, h869, h871, h964, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi2]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hlam, p988_0]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                rcases p988_3 (m.d 0 5) (by simp) with h1010 | h1010
                                                · linarith only [h1010, h423, hlam]
                                                · linarith only [h1010, h862, hlam]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h866, h869, h871, h964, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p988_1, u2ehi2]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                rcases p988_3 (m.d 0 5) (by simp) with h1014 | h1014
                                                · linarith only [h1014, h423, hlam]
                                                · linarith only [h1014, h865, hlam]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h862, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h868, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hlam, p988_0]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h964, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h0, h966, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p968_1, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h864, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h870, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hc35, hlam, hphi, ht23, p988_1, u2ehi4]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hlam, p988_0]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                rcases p988_3 (m.d 0 5) (by simp) with h1026 | h1026
                                                · rcases p988_3 (m.d 1 5) (by simp) with h1027 | h1027
                                                  · rcases p988_3 (m.d 2 5) (by simp) with h1028 | h1028
                                                    · linarith only [h1028, h964, hlam]
                                                    · linarith only [h1028, h966, hlam]
                                                  · linarith only [h1027, h871, hlam]
                                                · linarith only [h1026, h865, hlam]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h865, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h871, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h966, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [h967, hlam, p988_1]
                                              · have p988_0 := h988c.1
                                                have p988_1 := h988c.2.1
                                                have p988_2 := h988c.2.2.1
                                                have p988_3 := h988c.2.2.2
                                                linarith only [hlam, p988_0]
                                      · linarith only [h867, h981, hlam]
                                    · linarith only [h980, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h1040 | h1040
                                    · rcases p968_3 (m.d 1 2) (by simp) with h1041 | h1041
                                      · rcases p968_3 (m.d 2 3) (by simp) with h1042 | h1042
                                        · linarith only [h1042, h860, hlam]
                                        · rcases p968_3 (m.d 2 4) (by simp) with h1044 | h1044
                                          · linarith only [h1044, h861, hlam]
                                          · linarith only [h1044, h966, hlam]
                                      · linarith only [h1041, h868, hlam]
                                    · linarith only [h1040, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h860, h863, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p968_1, u3ehi3]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h1051 | h1051
                                    · linarith only [h0, h1051, hlam]
                                    · linarith only [h1051, h860, hlam]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h1054 | h1054
                                    · linarith only [h0, h1054, hlam]
                                    · linarith only [h1054, h861, hlam]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    rcases p968_3 (m.d 0 2) (by simp) with h1057 | h1057
                                    · linarith only [h0, h1057, hlam]
                                    · linarith only [h1057, h862, hlam]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h860, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h866, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h872, hlam, p968_1]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h964, hlam, p968_1]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h861, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h867, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hc24, hlam, hphi, p968_1, u2ehi2]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h863, h872, h964, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p968_1, u2ehi2]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h862, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h868, hlam, p968_0]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hc25, hlam, hphi, p968_1, u2ehi2]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [h966, hlam, p968_1]
                                  · have p968_0 := h968c.1
                                    have p968_1 := h968c.2.1
                                    have p968_2 := h968c.2.2.1
                                    have p968_3 := h968c.2.2.2
                                    linarith only [hlam, p968_0]
                                · linarith only [h0, h860, h863, h865, h872, h967, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1076 | h1076
                                · linarith only [h0, h1076, h860, h863, h872, h966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h1076, h872, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h423, h865, h871, hlam]
                      · linarith only [h869, h870, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1081 | h1081
                      · linarith only [h1081, h869, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1081, h423, h864, hlam]
                  · linarith only [h0, h860, h868, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h860, h867, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h860, h866, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1092 | h1092
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1093 | h1093
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1094 | h1094
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1095 | h1095
                              · linarith only [h1095, h861, h865, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1097 | h1097
                                · linarith only [h1093, h1097, h860, h861, h865, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases h2bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h0, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h0, h1094, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1099_1, u3ehi4]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    rcases p1099_3 (m.d 0 2) (by simp) with h1103 | h1103
                                    · rcases p1099_3 (m.d 1 2) (by simp) with h1104 | h1104
                                      · rcases p1099_3 (m.d 2 3) (by simp) with h1105 | h1105
                                        · linarith only [h1105, h860, hlam]
                                        · linarith only [h1093, h1105, hlam]
                                      · linarith only [h1088, h1104, hlam]
                                    · linarith only [h1103, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    rcases p1099_3 (m.d 0 2) (by simp) with h1110 | h1110
                                    · rcases p1099_3 (m.d 1 2) (by simp) with h1111 | h1111
                                      · rcases p1099_3 (m.d 2 3) (by simp) with h1112 | h1112
                                        · linarith only [h1112, h860, hlam]
                                        · linarith only [h1094, h1112, hlam]
                                      · linarith only [h1089, h1111, hlam]
                                    · linarith only [h1110, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1099_1, u3ehi2]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1094, h1097, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1099_1, u3ehi3]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    rcases p1099_3 (m.d 0 2) (by simp) with h1120 | h1120
                                    · linarith only [h0, h1120, hlam]
                                    · linarith only [h1120, h861, hlam]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    rcases p1099_3 (m.d 0 2) (by simp) with h1123 | h1123
                                    · linarith only [h0, h1123, hlam]
                                    · linarith only [h1123, h862, hlam]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h860, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1087, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h860, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1099_1, u2ehi3]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h0, h1094, h1097, h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1099_1, u3ehi3]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h861, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1088, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1093, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1095, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h862, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1089, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [h1094, hlam, p1099_0]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1099_1, u2ehi3]
                                  · have p1099_0 := h1099c.1
                                    have p1099_1 := h1099c.2.1
                                    have p1099_2 := h1099c.2.2.1
                                    have p1099_3 := h1099c.2.2.2
                                    linarith only [hlam, p1099_0]
                            · linarith only [h1093, h1094, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1087, h1090, h1092, h1093, h863, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1143 | h1143
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1144 | h1144
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1145 | h1145
                              · linarith only [h1145, h861, h865, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1147 | h1147
                                · linarith only [h1143, h1147, h861, h865, hlam]
                                · rcases h2bigk with h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h0, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h0, h1144, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1149_1, u3ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    rcases p1149_3 (m.d 0 2) (by simp) with h1153 | h1153
                                    · rcases p1149_3 (m.d 1 2) (by simp) with h1154 | h1154
                                      · rcases p1149_3 (m.d 2 3) (by simp) with h1155 | h1155
                                        · linarith only [h1155, h860, hlam]
                                        · linarith only [h1143, h1155, hlam]
                                      · linarith only [h1088, h1154, hlam]
                                    · linarith only [h1153, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    rcases p1149_3 (m.d 0 2) (by simp) with h1160 | h1160
                                    · rcases p1149_3 (m.d 1 2) (by simp) with h1161 | h1161
                                      · rcases p1149_3 (m.d 2 3) (by simp) with h1162 | h1162
                                        · linarith only [h1162, h860, hlam]
                                        · linarith only [h1144, h1162, hlam]
                                      · linarith only [h1089, h1161, hlam]
                                    · linarith only [h1160, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1144, h1147, h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1149_1, u3ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1144, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1149_1, u3ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    rcases p1149_3 (m.d 0 2) (by simp) with h1170 | h1170
                                    · linarith only [h0, h1170, hlam]
                                    · linarith only [h1170, h861, hlam]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    rcases p1149_3 (m.d 0 2) (by simp) with h1173 | h1173
                                    · linarith only [h0, h1173, hlam]
                                    · linarith only [h1173, h862, hlam]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h860, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1087, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h860, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1149_1, u2ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h0, h1145, h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1, u2ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h861, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1088, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1143, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1145, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h862, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1089, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [h1144, hlam, p1149_0]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1149_1, u2ehi3]
                                  · have p1149_0 := h1149c.1
                                    have p1149_1 := h1149c.2.1
                                    have p1149_2 := h1149c.2.2.1
                                    have p1149_3 := h1149c.2.2.2
                                    linarith only [hlam, p1149_0]
                            · linarith only [h1143, h1144, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h1143, h863, h865, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h1090, h1091, h860, h864, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1090, h863, h865, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h1089, h860, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1088, h862, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1087, h862, hc23, hlam, hphi, u2ehi4]
          · linarith only [h863, h864, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1199 | h1199
          · linarith only [h1199, h863, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1201 | h1201
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1202 | h1202
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1205 | h1205
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1207 | h1207
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1208 | h1208
                          · linarith only [h1208, h860, h863, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1210 | h1210
                            · linarith only [h1199, h1210, h860, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1213 | h1213
                                · rcases h2bigk with h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h0, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1217 | h1217
                                    · rcases p1214_3 (m.d 1 2) (by simp) with h1218 | h1218
                                      · rcases p1214_3 (m.d 2 3) (by simp) with h1219 | h1219
                                        · linarith only [h1219, hlam, p1214_0]
                                        · rcases p1214_3 (m.d 2 4) (by simp) with h1221 | h1221
                                          · linarith only [h1221, h861, hlam]
                                          · linarith only [h1208, h1221, hlam]
                                      · linarith only [h1202, h1218, hlam]
                                    · linarith only [h1217, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1226 | h1226
                                    · rcases p1214_3 (m.d 1 2) (by simp) with h1227 | h1227
                                      · rcases p1214_3 (m.d 2 3) (by simp) with h1228 | h1228
                                        · linarith only [h1228, h860, hlam]
                                        · rcases p1214_3 (m.d 2 4) (by simp) with h1230 | h1230
                                          · linarith only [h1230, hlam, p1214_0]
                                          · rcases p1214_3 (m.d 2 5) (by simp) with h1232 | h1232
                                            · linarith only [h1232, h862, hlam]
                                            · rcases h5bigk with h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c | h1234c
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [hlam, p1234_0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h423, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1199, h1202, h1205, h1213, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1234_1, u2ehi4]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1199, hlam, p1234_0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                rcases p1234_3 (m.d 0 5) (by simp) with h1239 | h1239
                                                · rcases p1234_3 (m.d 1 5) (by simp) with h1240 | h1240
                                                  · rcases p1234_3 (m.d 2 5) (by simp) with h1241 | h1241
                                                    · linarith only [h1241, h862, hlam]
                                                    · linarith only [h1212, h1241, hlam]
                                                  · linarith only [h1207, h1240, hlam]
                                                · linarith only [h1201, h1239, hlam]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                rcases p1234_3 (m.d 0 5) (by simp) with h1246 | h1246
                                                · linarith only [h1246, h423, hlam]
                                                · rcases p1234_3 (m.d 1 5) (by simp) with h1248 | h1248
                                                  · rcases p1234_3 (m.d 2 5) (by simp) with h1249 | h1249
                                                    · linarith only [h1204, h1249, hlam]
                                                    · rcases p1234_3 (m.d 3 5) (by simp) with h1251 | h1251
                                                      · linarith only [h1206, h1251, hlam]
                                                      · linarith only [h1199, h1251, hlam]
                                                  · linarith only [h1248, h423, hlam]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [hlam, p1234_0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                rcases p1234_3 (m.d 0 5) (by simp) with h1256 | h1256
                                                · linarith only [h1256, h423, hlam]
                                                · linarith only [h1256, h862, hlam]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1199, h1202, h1205, h1207, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1234_1, u3ehi0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                rcases p1234_3 (m.d 0 5) (by simp) with h1260 | h1260
                                                · linarith only [h1260, h423, hlam]
                                                · linarith only [h1201, h1260, hlam]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h862, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1204, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [hlam, p1234_0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1210, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h0, h1212, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1214_1, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h862, hc35, hlam, hphi, ht23, p1234_1, u2ehi4]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1206, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1202, h1206, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1234_1, u2ehi4]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [hlam, p1234_0]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                rcases p1234_3 (m.d 0 5) (by simp) with h1272 | h1272
                                                · linarith only [h1199, h1272, hlam]
                                                · linarith only [h1201, h1272, hlam]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1201, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1207, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1212, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [h1213, hlam, p1234_1]
                                              · have p1234_0 := h1234c.1
                                                have p1234_1 := h1234c.2.1
                                                have p1234_2 := h1234c.2.2.1
                                                have p1234_3 := h1234c.2.2.2
                                                linarith only [hlam, p1234_0]
                                      · linarith only [h1203, h1227, hlam]
                                    · linarith only [h1226, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1282 | h1282
                                    · rcases p1214_3 (m.d 1 2) (by simp) with h1283 | h1283
                                      · rcases p1214_3 (m.d 2 3) (by simp) with h1284 | h1284
                                        · linarith only [h1284, h860, hlam]
                                        · rcases p1214_3 (m.d 2 4) (by simp) with h1286 | h1286
                                          · linarith only [h1286, h861, hlam]
                                          · linarith only [h1212, h1286, hlam]
                                      · linarith only [h1204, h1283, hlam]
                                    · linarith only [h1282, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1214_1, u2ehi2]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1293 | h1293
                                    · linarith only [h0, h1293, hlam]
                                    · linarith only [h1293, h860, hlam]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1296 | h1296
                                    · linarith only [h0, h1296, hlam]
                                    · linarith only [h1296, h861, hlam]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    rcases p1214_3 (m.d 0 2) (by simp) with h1299 | h1299
                                    · linarith only [h0, h1299, hlam]
                                    · linarith only [h1299, h862, hlam]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h860, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1202, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1208, hlam, p1214_1]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1210, hlam, p1214_1]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h861, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1203, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h861, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1214_1, u2ehi2]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1202, h1205, h1210, h861, h863, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1214_1, u2ehi2]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h862, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1204, hlam, p1214_0]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1214_1, u2ehi2]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [h1212, hlam, p1214_1]
                                  · have p1214_0 := h1214c.1
                                    have p1214_1 := h1214c.2.1
                                    have p1214_2 := h1214c.2.2.1
                                    have p1214_3 := h1214c.2.2.2
                                    linarith only [hlam, p1214_0]
                                · linarith only [h1213, h863, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h1201, h1212, h863, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1201, h1202, h1203, h1205, h1207, h863, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1205, h1206, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1321 | h1321
                      · linarith only [h1205, h1321, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1323 | h1323
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1324 | h1324
                          · linarith only [h1205, h1324, h860, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1326 | h1326
                            · linarith only [h1199, h1326, h860, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1328 | h1328
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1329 | h1329
                                · rcases h2bigk with h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c | h1330c
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h0, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1333 | h1333
                                    · rcases p1330_3 (m.d 1 2) (by simp) with h1334 | h1334
                                      · rcases p1330_3 (m.d 2 3) (by simp) with h1335 | h1335
                                        · linarith only [h1335, hlam, p1330_0]
                                        · rcases p1330_3 (m.d 2 4) (by simp) with h1337 | h1337
                                          · linarith only [h1337, h861, hlam]
                                          · linarith only [h1324, h1337, hlam]
                                      · linarith only [h1202, h1334, hlam]
                                    · linarith only [h1333, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1342 | h1342
                                    · rcases p1330_3 (m.d 1 2) (by simp) with h1343 | h1343
                                      · rcases p1330_3 (m.d 2 3) (by simp) with h1344 | h1344
                                        · linarith only [h1344, h860, hlam]
                                        · rcases p1330_3 (m.d 2 4) (by simp) with h1346 | h1346
                                          · linarith only [h1346, hlam, p1330_0]
                                          · rcases p1330_3 (m.d 2 5) (by simp) with h1348 | h1348
                                            · linarith only [h1348, h862, hlam]
                                            · rcases h5bigk with h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h423, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1205, h1323, h1326, h423, hc34, hlam, hphi, p1350_1, u3ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1199, hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                rcases p1350_3 (m.d 0 5) (by simp) with h1355 | h1355
                                                · rcases p1350_3 (m.d 1 5) (by simp) with h1356 | h1356
                                                  · rcases p1350_3 (m.d 2 5) (by simp) with h1357 | h1357
                                                    · linarith only [h1357, h862, hlam]
                                                    · linarith only [h1328, h1357, hlam]
                                                  · linarith only [h1323, h1356, hlam]
                                                · linarith only [h1201, h1355, hlam]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1205, h1323, h1326, h862, hc34, hlam, hphi, ht23, p1350_1, u2ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1205, h1323, h1326, hc34, hlam, hphi, ht23, p1350_1, u2ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1321, hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                rcases p1350_3 (m.d 0 5) (by simp) with h1366 | h1366
                                                · linarith only [h1366, h423, hlam]
                                                · linarith only [h1201, h1366, hlam]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h862, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1204, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1326, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h0, h1328, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1330_1, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1326, h862, hc35, hlam, hphi, ht23, p1350_1, u2ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h0, h1326, h1328, h423, hc01, hc12, hc35, hlam, hphi, ht23, p1330_1, p1350_1, u2ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1326, hc35, hlam, hphi, ht23, p1350_1, u2ehi2]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [hlam, p1350_0]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                rcases p1350_3 (m.d 0 5) (by simp) with h1378 | h1378
                                                · linarith only [h1199, h1378, hlam]
                                                · linarith only [h1201, h1378, hlam]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1201, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1323, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1328, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [h1329, hlam, p1350_1]
                                              · have p1350_0 := h1350c.1
                                                have p1350_1 := h1350c.2.1
                                                have p1350_2 := h1350c.2.2.1
                                                have p1350_3 := h1350c.2.2.2
                                                linarith only [hlam, p1350_0]
                                      · linarith only [h1203, h1343, hlam]
                                    · linarith only [h1342, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1388 | h1388
                                    · rcases p1330_3 (m.d 1 2) (by simp) with h1389 | h1389
                                      · rcases p1330_3 (m.d 2 3) (by simp) with h1390 | h1390
                                        · linarith only [h1390, h860, hlam]
                                        · rcases p1330_3 (m.d 2 4) (by simp) with h1392 | h1392
                                          · linarith only [h1392, h861, hlam]
                                          · linarith only [h1328, h1392, hlam]
                                      · linarith only [h1204, h1389, hlam]
                                    · linarith only [h1388, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1330_1, u2ehi2]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1399 | h1399
                                    · linarith only [h0, h1399, hlam]
                                    · linarith only [h1399, h860, hlam]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1402 | h1402
                                    · linarith only [h0, h1402, hlam]
                                    · linarith only [h1402, h861, hlam]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    rcases p1330_3 (m.d 0 2) (by simp) with h1405 | h1405
                                    · linarith only [h0, h1405, hlam]
                                    · linarith only [h1405, h862, hlam]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h860, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1202, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1324, hlam, p1330_1]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1326, hlam, p1330_1]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h861, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1203, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h861, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1330_1, u2ehi2]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h0, h1326, h861, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1330_1, u2ehi2]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h862, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1204, hlam, p1330_0]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1330_1, u2ehi2]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [h1328, hlam, p1330_1]
                                  · have p1330_0 := h1330c.1
                                    have p1330_1 := h1330c.2.1
                                    have p1330_2 := h1330c.2.2.1
                                    have p1330_3 := h1330c.2.2.2
                                    linarith only [hlam, p1330_0]
                                · linarith only [h1329, h860, h863, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1201, h1328, h863, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1201, h1203, h1323, h863, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h1204, h860, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1203, h862, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1202, h862, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1433 | h1433
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1434 | h1434
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1435 | h1435
                          · linarith only [h1201, h1429, h1432, h1434, h1435, h860, h863, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1437 | h1437
                            · linarith only [h1201, h1429, h1432, h1434, h1437, h860, h863, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1439 | h1439
                              · linarith only [h1201, h1439, h860, h861, h863, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1441 | h1441
                                · linarith only [h1201, h1441, h860, h863, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h1434, h1441, h860, h863, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1432, h1434, h860, h863, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1432, h1433, h860, h863, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1446 | h1446
                      · linarith only [h1432, h1446, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1448 | h1448
                        · linarith only [h1201, h1432, h1448, h860, h863, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1450 | h1450
                          · linarith only [h1450, h860, h863, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1452 | h1452
                            · linarith only [h1201, h1452, h860, h863, hc45, hlam, hphi, ht34, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1454 | h1454
                              · linarith only [h1201, h1454, h861, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1456 | h1456
                                · linarith only [h1201, h1456, h863, hc34, hlam, hphi, u3ehi0]
                                · linarith only [h1456, h860, h863, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h1431, h860, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1430, h861, hlam]
              · linarith only [h0, h1429, h860, hlam]
      · linarith only [h860, h862, hc25, hlam, hphi, u2ehi2]
    · linarith only [h860, h861, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1464 | h1464
    · linarith only [h1464, h860, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1466 | h1466
      · linarith only [h1466, h860, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1468 | h1468
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1469 | h1469
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1472 | h1472
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1473 | h1473
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1474 | h1474
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1475 | h1475
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1477 | h1477
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1478 | h1478
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1479 | h1479
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1480 | h1480
                                · rcases h2bigk with h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h0, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h860, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1464, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    rcases p1481_3 (m.d 0 2) (by simp) with h1487 | h1487
                                    · linarith only [h0, h1487, hlam]
                                    · rcases p1481_3 (m.d 1 2) (by simp) with h1489 | h1489
                                      · rcases p1481_3 (m.d 2 3) (by simp) with h1490 | h1490
                                        · linarith only [h1471, h1490, hlam]
                                        · linarith only [h1490, h860, hlam]
                                      · linarith only [h0, h1489, hlam]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, h1477, h1479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, h1479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1471, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, h1471, h1479, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, h1471, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hc24, hlam, hphi, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1472, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1477, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1466, h1471, h1477, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1481_1, u2ehi0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1473, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1478, hlam, p1481_0]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [h1479, hlam, p1481_1]
                                  · have p1481_0 := h1481c.1
                                    have p1481_1 := h1481c.2.1
                                    have p1481_2 := h1481c.2.2.1
                                    have p1481_3 := h1481c.2.2.2
                                    linarith only [hlam, p1481_0]
                                · linarith only [h1464, h1470, h1471, h1477, h1480, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1464, h1479, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1478, h860, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1469, h1477, h860, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h1464, h1470, h1472, h1476, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1469, h1471, h1475, h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1468, h1471, h1474, h860, hlam]
                  · linarith only [h1471, h1473, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1471, h1472, h860, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1522 | h1522
                · linarith only [h1471, h1522, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1524 | h1524
                  · linarith only [h1471, h1524, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1527 | h1527
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1530 | h1530
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1531 | h1531
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1532 | h1532
                                · rcases h2bigk with h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c | h1533c
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h860, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1464, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1466, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1524, h1529, h1531, hc23, hlam, hphi, p1533_1, u2ehi0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1471, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1522, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1524, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1533_1, u2ehi0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1533_1, u2ehi1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1533_1, u2ehi3]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, h1524, hc01, hc23, hlam, hphi, ht12, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc24, hlam, hphi, p1533_1, u2ehi0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1529, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, h1524, h1529, hc01, hc23, hlam, hphi, ht12, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1533_1, u2ehi0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1530, hlam, p1533_0]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [h1531, hlam, p1533_1]
                                  · have p1533_0 := h1533c.1
                                    have p1533_1 := h1533c.2.1
                                    have p1533_2 := h1533c.2.2.1
                                    have p1533_3 := h1533c.2.2.2
                                    linarith only [hlam, p1533_0]
                                · rcases h2bigk with h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h0, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h860, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1464, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1466, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1471, hc23, hlam, hphi, p1559_1, u2ehi0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1471, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1522, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1524, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1559_1, u2ehi0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1559_1, u2ehi1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hc23, hlam, hphi, p1559_1, u2ehi3]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h0, h1524, hc01, hc23, hlam, hphi, ht12, p1559_1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hc24, hlam, hphi, p1559_1, u2ehi0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h0, hc01, hc24, hlam, hphi, ht12, p1559_1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1529, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h0, h1524, h1529, hc01, hc23, hlam, hphi, ht12, p1559_1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hc25, hlam, hphi, p1559_1, u2ehi0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1559_1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1530, hlam, p1559_0]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [h1531, hlam, p1559_1]
                                  · have p1559_0 := h1559c.1
                                    have p1559_1 := h1559c.2.1
                                    have p1559_2 := h1559c.2.2.1
                                    have p1559_3 := h1559c.2.2.2
                                    linarith only [hlam, p1559_0]
                              · linarith only [h1468, h1470, h1531, h860, hc23, hlam, hphi, u2ehi3]
                            · linarith only [h1530, h860, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h0, h1468, h1471, h1529, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h1464, h1470, h1522, h1528, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h1469, h1471, h1527, h860, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h1468, h1471, h1526, h860, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1591 | h1591
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1592 | h1592
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1593 | h1593
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1594 | h1594
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1596 | h1596
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1597 | h1597
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1598 | h1598
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1599 | h1599
                              · linarith only [h1468, h1470, h1591, h1597, h1599, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1464, h1599, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1469, h1598, h860, hlam]
                          · linarith only [h1469, h1597, h860, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h1464, h1592, h1596, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1469, h1591, h1595, h860, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1469, h1591, h1594, h860, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1469, h1591, h1593, h860, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1591, h1592, h860, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1609 | h1609
                · linarith only [h1591, h1609, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1611 | h1611
                  · linarith only [h1591, h1611, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1613 | h1613
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1614 | h1614
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1615 | h1615
                        · linarith only [h1464, h1470, h1591, h1613, h1615, hc23, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1617 | h1617
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1618 | h1618
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1619 | h1619
                              · linarith only [h1609, h1615, h1619, hc24, hlam, hphi, u2ehi1]
                              · linarith only [h1464, h1619, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1469, h1618, h860, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1468, h1617, h860, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1613, h1614, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1468, h1470, h1613, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h1468, h1469, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1627 | h1627
          · linarith only [h1468, h1627, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1630 | h1630
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1632 | h1632
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1634 | h1634
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1635 | h1635
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1636 | h1636
                          · linarith only [h1468, h1630, h1636, h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1636, h860, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1468, h1629, h1630, h1631, h1633, h1635, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1633, h1634, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1630, h1633, h860, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1630, h1632, h860, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1630, h1631, h860, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1644 | h1644
                · linarith only [h1630, h1644, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1646 | h1646
                  · linarith only [h1630, h1646, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1648 | h1648
                    · linarith only [h1468, h1630, h1648, h860, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
                      · linarith only [h1648, h1650, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1652 | h1652
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1653 | h1653
                          · linarith only [h1630, h1648, h1653, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h1653, h860, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h1468, h1629, h1644, h1652, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1657 | h1657
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1658 | h1658
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1659 | h1659
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1660 | h1660
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1661 | h1661
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1662 | h1662
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1663 | h1663
                          · linarith only [h1468, h1657, h1663, h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1663, h860, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1464, h1658, h1662, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                      · linarith only [h1660, h1661, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1657, h1660, h860, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1657, h1659, h860, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1657, h1658, h860, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1671 | h1671
                · linarith only [h1657, h1671, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1673 | h1673
                  · linarith only [h1657, h1673, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
                    · linarith only [h1468, h1657, h1675, h860, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
                      · linarith only [h1675, h1677, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1679 | h1679
                        · linarith only [h1468, h1629, h1671, h1679, h860, hc24, hlam, hphi, u2ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1681 | h1681
                          · linarith only [h1468, h1681, h860, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1681, h860, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 3368000 in
set_option maxHeartbeats 3368000 in
theorem r1l7_22_13_15_M_IR_L_R_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h423 | h423
  · exact r1l7_22_13_15_M_IR_L_R_L_I_x1_x0 m hb2 hb3 hb5 h0 h423
  · exact r1l7_22_13_15_M_IR_L_R_L_I_x1_x1 m hb2 hb3 hb5 h0 h423

set_option maxHeartbeats 3368000 in
set_option maxHeartbeats 3368000 in
theorem r1l7_22_13_15_M_IR_L_R_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_M_IR_L_R_L_I_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_M_IR_L_R_L_I_x1 m hb2 hb3 hb5 h0

end R2N4
