import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h831 | h831
  · rcases m.htr 0 2 5 (by decide) (by decide) with h832 | h832
    · rcases m.htr 0 3 4 (by decide) (by decide) with h833 | h833
      · rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
        · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
          · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
            · linarith only [h0, h3, h831, h836, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
              · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h843 | h843
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h844 | h844
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h845 | h845
                            · linarith only [h0, h3, h838, h845, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                            · linarith only [h3, h831, h835, h843, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h3, h844, hc02, hlam, hphi, ht23, u3elo4]
                        · linarith only [h3, h843, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h3, h831, h835, h842, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h834, h841, hc13, hlam, hphi, u3elo0]
                  · linarith only [h3, h833, h836, h840, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h3, h832, h838, h839, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h3, h831, h838, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h855 | h855
            · linarith only [h0, h3, h831, h855, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h857 | h857
              · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
                · rcases m.htr 1 3 4 (by decide) (by decide) with h859 | h859
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h860 | h860
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                      · linarith only [h0, h3, h831, h835, h857, h861, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h864 | h864
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h865 | h865
                            · linarith only [h3, h831, h861, h865, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h867 | h867
                              · linarith only [h3, h833, h835, h867, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · rcases h2bigk with h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c | h869c
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h3, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h3, h863, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h3, h864, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h0, hlam, p869_1]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h855, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h855, h863, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p869_1, u3elo1]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h0, h3, h864, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h863, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h864, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p869_1, u3elo2]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h831, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h857, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h863, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h865, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h832, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h858, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h864, hlam, p869_0]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [h832, h863, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p869_1]
                                · have p869_0 := h869c.1
                                  have p869_1 := h869c.2.1
                                  have p869_2 := h869c.2.2.1
                                  have p869_3 := h869c.2.2.2
                                  linarith only [hlam, p869_0]
                          · linarith only [h0, h3, h857, h863, h864, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h3, h857, h863, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h3, h832, h834, h860, hc13, hlam, hphi, u3elo2]
                  · linarith only [h833, h835, h855, h857, h859, hc24, hc45, hlam, hphi]
                · linarith only [h3, h832, h857, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h3, h831, h857, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h3, h832, h834, hlam]
      · linarith only [h3, h831, h833, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h903 | h903
      · rcases m.htr 0 3 5 (by decide) (by decide) with h904 | h904
        · rcases m.htr 0 4 5 (by decide) (by decide) with h905 | h905
          · linarith only [h831, h832, h905, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h907 | h907
            · linarith only [h0, h3, h907, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
              · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                · linarith only [h0, h832, h910, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h912 | h912
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h914 | h914
                      · linarith only [h0, h3, h905, h909, h914, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h916 | h916
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h917 | h917
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h918 | h918
                            · linarith only [h831, h832, h914, h917, h918, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h920 | h920
                              · linarith only [h832, h918, h920, hc02, hlam, hphi, ht23, u3elo3]
                              · rcases h2bigk with h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c | h922c
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h909, h916, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p922_1]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h3, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h3, h916, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h832, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h0, hlam, p922_1]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h907, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h910, h913, h916, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p922_1, u3elo1]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h910, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h916, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h831, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h909, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h916, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h918, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h0, h909, h916, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p922_1]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h909, h916, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p922_1]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h917, hlam, p922_0]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [h916, h917, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p922_1, u3elo2]
                                · have p922_0 := h922c.1
                                  have p922_1 := h922c.2.1
                                  have p922_2 := h922c.2.2.1
                                  have p922_3 := h922c.2.2.2
                                  linarith only [hlam, p922_0]
                          · linarith only [h1, h3, h913, h917, hlam]
                        · linarith only [h3, h916, hc02, hlam, hphi, ht23, u3elo3]
                    · linarith only [h904, h913, hc13, hlam, hphi, u3elo0]
                  · linarith only [h3, h903, h907, h909, h912, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h3, h831, h909, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h953 | h953
          · linarith only [h831, h832, h953, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h955 | h955
            · linarith only [h0, h3, h904, h955, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h957 | h957
              · rcases m.htr 1 2 5 (by decide) (by decide) with h958 | h958
                · linarith only [h832, h955, h958, hc02, hlam, hphi, ht23, u3elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h961 | h961
                    · linarith only [h1, h904, h961, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h963 | h963
                      · linarith only [h0, h3, h953, h957, h963, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h965 | h965
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h966 | h966
                          · linarith only [h3, h904, h966, hc02, hlam, hphi, ht23, u3elo2]
                          · linarith only [h0, h3, h957, h965, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h3, h957, h965, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h3, h831, h903, h960, hc13, hlam, hphi, u3elo2]
              · linarith only [h3, h831, h904, h957, hc12, hlam, hphi, ht23, u3elo4]
      · linarith only [h3, h831, h903, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h973 | h973
    · rcases m.htr 0 3 4 (by decide) (by decide) with h974 | h974
      · rcases m.htr 0 3 5 (by decide) (by decide) with h975 | h975
        · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
          · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
            · linarith only [h0, h3, h973, h977, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
              · linarith only [h831, h973, h977, h979, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h981 | h981
                · rcases m.htr 1 3 4 (by decide) (by decide) with h982 | h982
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h985 | h985
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h986 | h986
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h987 | h987
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h988 | h988
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
                                  linarith only [h831, h985, hc12, hlam, hphi, ht23, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h3, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h831, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h831, h985, h986, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, hlam, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h977, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h979, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, h986, hc01, hc35, hlam, hphi, ht0b, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h986, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h0, h981, h986, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h981, h986, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h985, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h985, h986, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p989_1, u3elo2]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h973, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h981, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h986, hlam, p989_0]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [h987, hlam, p989_1]
                                · have p989_0 := h989c.1
                                  have p989_1 := h989c.2.1
                                  have p989_2 := h989c.2.2.1
                                  have p989_3 := h989c.2.2.2
                                  linarith only [hlam, p989_0]
                              · linarith only [h3, h973, h987, h988, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · linarith only [h1, h831, h982, h984, h987, hc02, hlam, hphi, ht23, u3elo0]
                          · linarith only [h0, h831, h981, h985, h986, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h0, h3, h981, h985, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h3, h973, h976, h979, h981, h984, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h3, h975, h983, hc13, hlam, hphi, u3elo2]
                  · linarith only [h3, h974, h977, h981, h982, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h3, h973, h981, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h831, h973, h976, hlam]
        · linarith only [h831, h973, h974, h975, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1025 | h1025
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1026 | h1026
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1027 | h1027
            · linarith only [h0, h1027, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1029 | h1029
              · linarith only [h1027, h1029, h831, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1031 | h1031
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
                  · linarith only [h1, h1032, h974, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1034 | h1034
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1036 | h1036
                        · linarith only [h0, h1031, h1036, h3, h974, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h0, h1031, h1036, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h1026, h1032, h1035, h974, hc13, hlam, hphi, u3elo3]
                    · linarith only [h1025, h1027, h1031, h1034, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                · linarith only [h1031, h3, h973, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h1026, h831, h973, hlam]
        · linarith only [h1025, h3, h973, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1044 | h1044
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1045 | h1045
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1046 | h1046
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1047 | h1047
            · linarith only [h0, h1047, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1049 | h1049
              · linarith only [h1047, h1049, h831, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1051 | h1051
                · linarith only [h0, h1051, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1054 | h1054
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1055 | h1055
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1057 | h1057
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1058 | h1058
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1059 | h1059
                              · rcases h2bigk with h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1058, h973, hc12, hc24, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h3, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h831, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h973, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h0, hlam, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1047, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1049, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1051, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hc02, hc23, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p1060_1, u3elo2]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1060_1, u3elo2]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h0, h973, hc12, hlam, hphi, ht23, p1060_1, u3elo2]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1056, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h0, h1056, h973, hc12, hlam, hphi, ht23, p1060_1, u3elo2]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1057, hlam, p1060_0]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [h1058, hlam, p1060_1]
                                · have p1060_0 := h1060c.1
                                  have p1060_1 := h1060c.2.1
                                  have p1060_2 := h1060c.2.2.1
                                  have p1060_3 := h1060c.2.2.2
                                  linarith only [hlam, p1060_0]
                              · rcases h2bigk with h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h3, hc12, hlam, hphi, ht23, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h3, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h831, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h973, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h0, hlam, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1047, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1049, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1051, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1056, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h0, h1056, h973, hc12, hlam, hphi, ht23, p1086_1, u3elo2]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1057, hlam, p1086_0]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [h1058, hlam, p1086_1]
                                · have p1086_0 := h1086c.1
                                  have p1086_1 := h1086c.2.1
                                  have p1086_2 := h1086c.2.2.1
                                  have p1086_3 := h1086c.2.2.2
                                  linarith only [hlam, p1086_0]
                            · linarith only [h1046, h1058, h831, hlam]
                          · linarith only [h0, h1057, h3, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h1056, h3, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1044, h1046, h1049, h1055, h3, hc12, hlam, hphi, ht23, u3elo2]
                    · linarith only [h1045, h1054, h3, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1044, h1047, h1053, h3, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
            · linarith only [h0, h1118, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1120 | h1120
              · linarith only [h1118, h1120, h831, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1122 | h1122
                · linarith only [h0, h1046, h1122, h831, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
                      · linarith only [h0, h1046, h1124, h1126, h831, hc12, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1128 | h1128
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1129 | h1129
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                            · linarith only [h0, h1046, h1128, h1130, h831, hc12, hlam, hphi, ht23, u3elo2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1132 | h1132
                              · linarith only [h0, h1130, h1132, h831, hc12, hlam, hphi, ht23, u3elo3]
                              · rcases h2bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h831, hc12, hc24, hlam, hphi, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h3, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h831, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h973, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h0, hlam, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1118, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1120, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1122, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, p1134_1, u3elo2]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, p1134_1, u3elo2]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1134_1, u3elo2]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1134_1, u3elo2]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h0, hc12, hc24, hlam, hphi, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc12, hc24, hlam, hphi, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1128, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1130, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h0, hc12, hc25, hlam, hphi, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hc12, hc25, hlam, hphi, p1134_1]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1129, hlam, p1134_0]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [h1120, h1129, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1134_1, u3elo2]
                                · have p1134_0 := h1134c.1
                                  have p1134_1 := h1134c.2.1
                                  have p1134_2 := h1134c.2.2.1
                                  have p1134_3 := h1134c.2.2.2
                                  linarith only [hlam, p1134_0]
                          · linarith only [h1, h1125, h1129, h3, hlam]
                        · linarith only [h0, h1128, h3, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1045, h1125, h3, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1044, h1118, h1124, h3, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1164 | h1164
          · linarith only [h1044, h1045, h1164, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1166 | h1166
            · linarith only [h0, h1166, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
              · linarith only [h1166, h1168, h831, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1170 | h1170
                · linarith only [h0, h1170, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1172 | h1172
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1173 | h1173
                    · linarith only [h1, h1045, h1173, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1175 | h1175
                      · linarith only [h1, h1045, h1164, h1172, h1175, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1177 | h1177
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1178 | h1178
                          · linarith only [h1045, h1178, hc03, hlam, hphi, u3elo2]
                          · linarith only [h0, h1178, h3, hc12, hlam, hphi, ht23, u3elo4]
                        · linarith only [h0, h1177, h3, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1044, h1045, h1172, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1183 | h1183
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1184 | h1184
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
            · linarith only [h0, h1185, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1187 | h1187
              · linarith only [h0, h1187, h831, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1189 | h1189
                · linarith only [h0, h1189, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
                  · linarith only [h1044, h1183, h1191, h973, hc02, hlam, hphi, ht23, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1193 | h1193
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1194 | h1194
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1195 | h1195
                        · linarith only [h1, h1044, h1193, h1195, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h0, h1195, h3, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1044, h1183, h1184, h1187, h1194, hc12, hlam, hphi, ht23, u3elo3]
                    · linarith only [h1044, h1183, h1193, hc13, hlam, hphi, u3elo3]
          · linarith only [h1044, h1183, h1184, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1201 | h1201
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1202 | h1202
            · linarith only [h0, h1202, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1204 | h1204
              · linarith only [h0, h1204, h831, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1206 | h1206
                · linarith only [h0, h1206, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1208 | h1208
                  · linarith only [h1044, h1208, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
                    · linarith only [h1, h1183, h1210, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1212 | h1212
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1213 | h1213
                        · linarith only [h0, h1044, h1213, h3, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h1213, h3, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1044, h1201, h1204, h1212, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
            · linarith only [h0, h1217, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1219 | h1219
              · linarith only [h0, h1219, h831, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                · linarith only [h0, h1221, h973, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1223 | h1223
                  · linarith only [h1, h1044, h1223, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1225 | h1225
                    · linarith only [h1, h1183, h1225, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1227 | h1227
                      · linarith only [h1044, h1201, h1223, h1227, h3, hc02, hlam, hphi, ht23, u3elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1229 | h1229
                        · linarith only [h0, h1044, h1229, h3, hc12, hlam, hphi, ht23, u3elo2]
                        · linarith only [h0, h1229, h3, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1232 | h1232
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1233 | h1233
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1234 | h1234
      · linarith only [h0, h1234, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1236 | h1236
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1237 | h1237
          · linarith only [h1, h1237, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1239 | h1239
            · linarith only [h0, h1233, h1239, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
              · linarith only [h0, h1237, h1241, h2, hc23, hlam, hphi, u3elo4]
              · linarith only [h1232, h1234, h1241, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1244 | h1244
          · linarith only [h0, h1236, h1244, h2, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1246 | h1246
            · linarith only [h0, h1233, h1246, h2, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1248 | h1248
              · linarith only [h0, h1244, h1248, h2, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h1232, h1244, h1248, h2, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1251 | h1251
      · linarith only [h0, h1251, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1253 | h1253
        · linarith only [h1232, h1233, h1253, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1255 | h1255
          · linarith only [h1, h1253, h1255, h2, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1257 | h1257
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
              · linarith only [h0, h1253, h1257, h1258, h2, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h1232, h1253, h1257, h1258, h2, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1261 | h1261
              · linarith only [h0, h1255, h1261, h2, hc23, hlam, hphi, u3elo4]
              · linarith only [h1232, h1233, h1261, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1264 | h1264
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1265 | h1265
      · linarith only [h0, h1265, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1267 | h1267
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1268 | h1268
          · linarith only [h1, h1268, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1270 | h1270
            · linarith only [h0, h1232, h1264, h1268, h1270, h2, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
              · linarith only [h0, h1232, h1268, h1272, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1275 | h1275
                  · linarith only [h1, h1265, h1272, h1275, h2, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1277 | h1277
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1278 | h1278
                      · linarith only [h1, h1268, h1278, h2, hlam]
                      · linarith only [h1, h1272, h1278, h2, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h1267, h1272, h1274, h1277, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h1232, h1264, h1274, hc12, hc23, hlam, hphi]
        · linarith only [h1232, h1264, h1267, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1284 | h1284
      · linarith only [h0, h1284, h2, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1286 | h1286
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1287 | h1287
          · linarith only [h1, h1287, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1289 | h1289
            · linarith only [h0, h1286, h1287, h1289, h2, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1291 | h1291
              · linarith only [h0, h1264, h1286, h1287, h1291, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1293 | h1293
                · linarith only [h0, h1264, h1293, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1295 | h1295
                  · linarith only [h1, h1284, h1291, h1295, h2, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1297 | h1297
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1298 | h1298
                      · linarith only [h1, h1287, h1298, h2, hlam]
                      · linarith only [h1, h1293, h1297, h1298, h2, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h1286, h1291, h1297, hc12, hlam, hphi, ht23, u3elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1302 | h1302
          · linarith only [h1, h1286, h1302, h2, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1304 | h1304
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
              · linarith only [h0, h1232, h1305, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1307 | h1307
                · linarith only [h1, h1264, h1304, h1305, h1307, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1309 | h1309
                  · linarith only [h0, h1284, h1309, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                    · linarith only [h1, h1286, h1311, h2, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1313 | h1313
                      · linarith only [h0, h1302, h1313, h2, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1, h1305, h1313, h2, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
              · linarith only [h0, h1302, h1316, h2, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
                · linarith only [h0, h1264, h1318, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h0, h1284, h1320, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1322 | h1322
                    · linarith only [h1, h1232, h1286, h1302, h1322, h2, hc02, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1324 | h1324
                      · linarith only [h0, h1, h1302, h1324, h2, hc12, hlam, hphi, ht23, u3elo0]
                      · linarith only [h1, h1316, h1324, h2, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x0 m hb2 hb3 hb5 h0 h1
  · exact r1l7_22_13_15_H_I_L_0_L_I_x0_x1 m hb2 hb3 hb5 h0 h1

end R2N4
