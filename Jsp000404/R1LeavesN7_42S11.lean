import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h910 | h910
  · rcases m.htr 0 2 5 (by decide) (by decide) with h911 | h911
    · rcases m.htr 0 3 4 (by decide) (by decide) with h912 | h912
      · rcases m.htr 0 3 5 (by decide) (by decide) with h913 | h913
        · rcases m.htr 1 2 3 (by decide) (by decide) with h914 | h914
          · linarith only [h0, h2, h910, h914, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h916 | h916
            · rcases m.htr 1 2 5 (by decide) (by decide) with h917 | h917
              · rcases m.htr 1 3 4 (by decide) (by decide) with h918 | h918
                · rcases m.htr 1 3 5 (by decide) (by decide) with h919 | h919
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h920 | h920
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h921 | h921
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h922 | h922
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h923 | h923
                          · rcases h2bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h916, h920, h923, hc02, hc45, hlam, hphi, ht0b, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, h920, h923, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, hlam, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h914, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h920, h923, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, h2, h921, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h920, h923, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              rcases p924_3 (m.d 0 2) (by simp) with h939 | h939
                              · linarith only [h2, h939, hlam]
                              · linarith only [h911, h939, hlam]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h910, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h916, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h920, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h0, h916, h921, h923, hc02, hc45, hlam, hphi, ht0b, ht5b, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h911, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h917, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h921, hlam, p924_0]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [h922, hlam, p924_1]
                            · have p924_0 := h924c.1
                              have p924_1 := h924c.2.1
                              have p924_2 := h924c.2.2.1
                              have p924_3 := h924c.2.2.2
                              linarith only [hlam, p924_0]
                          · linarith only [h0, h2, h916, h922, h923, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                          · linarith only [h920, h922, h953, hlam]
                          · rcases h2bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h2, hc12, hc23, hlam, hphi, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h2, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h2, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h2, h922, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, hlam, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h914, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, h2, h922, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              rcases p955_3 (m.d 0 2) (by simp) with h969 | h969
                              · linarith only [h2, h969, hlam]
                              · linarith only [h910, h969, hlam]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              rcases p955_3 (m.d 0 2) (by simp) with h972 | h972
                              · linarith only [h2, h972, hlam]
                              · linarith only [h911, h972, hlam]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h910, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h916, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h920, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h922, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h911, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h917, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h921, hlam, p955_0]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [h0, h917, h920, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p955_1]
                            · have p955_0 := h955c.1
                              have p955_1 := h955c.2.1
                              have p955_2 := h955c.2.2.1
                              have p955_3 := h955c.2.2.2
                              linarith only [hlam, p955_0]
                      · linarith only [h2, h921, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h2, h912, h920, hlam]
                  · linarith only [h913, h914, h916, h919, hc24, hlam, hphi, ht45, u5elo0]
                · linarith only [h914, h916, h918, hlam]
              · linarith only [h916, h917, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h2, h910, h916, hc12, hc23, hlam, hphi]
        · linarith only [h912, h913, hc34, hlam, hphi, ht45, u5elo3]
      · linarith only [h2, h910, h912, hlam]
    · linarith only [h910, h911, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h994 | h994
    · rcases m.htr 0 3 4 (by decide) (by decide) with h995 | h995
      · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
        · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
          · linarith only [h0, h2, h994, h997, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
            · linarith only [h0, h910, h999, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1001 | h1001
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1003 | h1003
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1005 | h1005
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1006 | h1006
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1007 | h1007
                          · rcases h2bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1001, h1005, h1007, hc02, hc45, hlam, hphi, ht0b, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h2, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h910, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1004, h1005, h1007, h910, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h997, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h999, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h1005, h1007, hc01, hc45, hlam, hphi, ht0b, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1005, h1007, h910, h994, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              rcases p1008_3 (m.d 0 2) (by simp) with h1023 | h1023
                              · linarith only [h1023, h2, hlam]
                              · linarith only [h1023, h994, hlam]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h1001, h1005, h1007, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1001, h1005, h1007, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1004, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              rcases p1008_3 (m.d 0 2) (by simp) with h1030 | h1030
                              · linarith only [h1030, h910, hlam]
                              · linarith only [h1030, h994, hlam]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h994, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1001, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1005, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1006, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                          · rcases h2bigk with h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1001, h1006, h1007, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h2, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h910, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1004, h1006, h1007, h910, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h0, hlam, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h997, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h999, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1006, h1007, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1006, h1007, h910, h994, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1006, h1007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h0, h1001, h1006, h1007, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1001, h1006, h1007, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1004, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1004, h1006, h1007, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h994, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1001, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1005, hlam, p1038_0]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [h1006, hlam, p1038_1]
                            · have p1038_0 := h1038c.1
                              have p1038_1 := h1038c.2.1
                              have p1038_2 := h1038c.2.2.1
                              have p1038_3 := h1038c.2.2.2
                              linarith only [hlam, p1038_0]
                        · linarith only [h1006, h910, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1001, h1005, h2, hc25, hlam, hphi, u5elo3]
                    · linarith only [h0, h1001, h1004, h2, h995, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1002, h1003, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1068 | h1068
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1069 | h1069
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1070 | h1070
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1071 | h1071
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1072 | h1072
                          · rcases h2bigk with h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1001, h1070, h1072, hc02, hc45, hlam, hphi, ht0b, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h2, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h910, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1070, h1072, h910, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h0, hlam, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h997, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h999, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1002, h1070, h1072, h995, h997, hc04, hc45, hlam, hphi, ht0b, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h0, h1001, h1070, h1072, h910, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              rcases p1073_3 (m.d 0 2) (by simp) with h1088 | h1088
                              · linarith only [h1088, h2, hlam]
                              · linarith only [h1088, h994, hlam]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h0, h1001, h1070, h1072, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1001, h1070, h1072, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1069, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              rcases p1073_3 (m.d 0 2) (by simp) with h1095 | h1095
                              · linarith only [h1095, h910, hlam]
                              · linarith only [h1095, h994, hlam]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h994, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1001, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1070, hlam, p1073_0]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [h1071, hlam, p1073_1]
                            · have p1073_0 := h1073c.1
                              have p1073_1 := h1073c.2.1
                              have p1073_2 := h1073c.2.2.1
                              have p1073_3 := h1073c.2.2.2
                              linarith only [hlam, p1073_0]
                          · linarith only [h1002, h1072, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1071, h910, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1002, h1070, h2, h995, h997, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1069, h2, h995, hlam]
                  · linarith only [h1001, h1068, h997, hc25, hlam, hphi, u5elo3]
              · linarith only [h1001, h2, h994, hc12, hc23, hlam, hphi]
        · linarith only [h995, h996, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1110 | h1110
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
          · linarith only [h0, h1111, h2, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1113 | h1113
            · linarith only [h0, h1113, h910, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
                · linarith only [h0, h1, h1115, h1116, h2, h995, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1121 | h1121
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
                          · rcases h2bigk with h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1115, h1119, h1120, h1122, h2, h995, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h2, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h910, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1119, h1120, h1122, h2, h995, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h0, hlam, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1111, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1113, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h0, h1120, h1122, hc01, hc45, hlam, hphi, ht0b, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1119, h995, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              rcases p1123_3 (m.d 0 2) (by simp) with h1138 | h1138
                              · linarith only [h1138, h2, hlam]
                              · linarith only [h1138, h994, hlam]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h0, h1115, h1120, h1122, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1115, h1120, h1122, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1119, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              rcases p1123_3 (m.d 0 2) (by simp) with h1145 | h1145
                              · linarith only [h1145, h910, hlam]
                              · linarith only [h1145, h994, hlam]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h994, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1115, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1120, hlam, p1123_0]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [h1121, hlam, p1123_1]
                            · have p1123_0 := h1123c.1
                              have p1123_1 := h1123c.2.1
                              have p1123_2 := h1123c.2.2.1
                              have p1123_3 := h1123c.2.2.2
                              linarith only [hlam, p1123_0]
                          · linarith only [h0, h1115, h1120, h1122, h2, h995, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1115, h1120, h1121, h910, hc35, hlam, hphi, u5elo4]
                      · linarith only [h1120, h2, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1156 | h1156
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1158 | h1158
                          · rcases h2bigk with h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1115, h1119, h1156, h1158, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h2, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h910, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, h1156, h1158, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h0, hlam, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1111, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1113, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h0, h1156, h1158, hc01, hc45, hlam, hphi, ht0b, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, hc02, hc34, hlam, hphi, ht23, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, hc12, hc34, hlam, hphi, ht23, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, hlam, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, h1156, h1158, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h0, h1115, h1119, h1156, h1158, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1115, h1119, h1156, h1158, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1119, h2, hc03, hc34, hlam, hphi, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              rcases p1159_3 (m.d 0 2) (by simp) with h1179 | h1179
                              · linarith only [h1179, h910, hlam]
                              · linarith only [h1179, h994, hlam]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h994, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1115, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1156, hlam, p1159_0]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [h1157, hlam, p1159_1]
                            · have p1159_0 := h1159c.1
                              have p1159_1 := h1159c.2.1
                              have p1159_2 := h1159c.2.2.1
                              have p1159_3 := h1159c.2.2.2
                              linarith only [hlam, p1159_0]
                          · linarith only [h0, h1115, h1119, h1156, h1158, h910, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1115, h1119, h1156, h1157, h2, hc35, hlam, hphi, u5elo4]
                      · linarith only [h0, h1115, h1156, h2, hc25, hlam, hphi, u5elo3]
                  · linarith only [h1111, h1115, h1118, hc25, hlam, hphi, u5elo3]
              · linarith only [h1115, h2, h994, h995, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1110, h2, h994, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1193 | h1193
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1194 | h1194
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1195 | h1195
          · linarith only [h0, h1195, h2, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1197 | h1197
            · linarith only [h0, h1197, h910, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
              · linarith only [h0, h1199, h994, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1201 | h1201
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1202 | h1202
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1203 | h1203
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1205 | h1205
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1206 | h1206
                          · rcases h2bigk with h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h994, hc12, hlam, hphi, ht23, ht34, ht45, p1207_1, u5elo2]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h2, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h910, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h994, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1195, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1197, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1199, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, h910, hc12, hc23, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, h994, hc12, hc23, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1203, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, h1203, h994, hc12, hc23, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1207_1, u5elo2]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1204, hlam, p1207_0]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [h1205, hlam, p1207_1]
                            · have p1207_0 := h1207c.1
                              have p1207_1 := h1207c.2.1
                              have p1207_2 := h1207c.2.2.1
                              have p1207_3 := h1207c.2.2.2
                              linarith only [hlam, p1207_0]
                          · rcases h2bigk with h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h2, hc12, hc23, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h2, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h910, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h994, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1195, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1197, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1199, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, h910, hc12, hc23, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1205, h1206, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1203, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, h1203, h994, hc12, hc23, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1233_1, u5elo2]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1204, hlam, p1233_0]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [h1205, hlam, p1233_1]
                            · have p1233_0 := h1233c.1
                              have p1233_1 := h1233c.2.1
                              have p1233_2 := h1233c.2.2.1
                              have p1233_3 := h1233c.2.2.2
                              linarith only [hlam, p1233_0]
                        · linarith only [h0, h1205, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1204, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1193, h1203, h2, hlam]
                  · linarith only [h1201, h1202, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1263 | h1263
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1265 | h1265
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1267 | h1267
                          · rcases h2bigk with h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h2, hc12, hc23, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h2, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h910, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h994, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h0, hlam, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1195, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1197, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1199, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1193, h1201, h910, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h0, h994, hc12, hc23, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1264, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h0, h1264, h994, hc12, hc23, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1268_1, u5elo2]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1265, hlam, p1268_0]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [h1266, hlam, p1268_1]
                            · have p1268_0 := h1268c.1
                              have p1268_1 := h1268c.2.1
                              have p1268_2 := h1268c.2.2.1
                              have p1268_3 := h1268c.2.2.2
                              linarith only [hlam, p1268_0]
                          · linarith only [h1201, h1267, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h1266, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1201, h1263, h1265, h2, hc03, hc34, hlam, hphi]
                    · linarith only [h1193, h1264, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1298 | h1298
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1299 | h1299
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1300 | h1300
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1301 | h1301
                          · rcases h2bigk with h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c | h1302c
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h2, hc12, hc23, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h2, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h910, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h994, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h0, hlam, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1195, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1197, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1199, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h0, h910, hc12, hc23, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1194, h1263, h994, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1298, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1194, h1195, h1263, h1298, h994, hc12, hc23, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1302_1, u5elo2]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1299, hlam, p1302_0]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [h1300, hlam, p1302_1]
                            · have p1302_0 := h1302c.1
                              have p1302_1 := h1302c.2.1
                              have p1302_2 := h1302c.2.2.1
                              have p1302_3 := h1302c.2.2.2
                              linarith only [hlam, p1302_0]
                          · linarith only [h1195, h1201, h1301, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1300, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1194, h1299, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                    · linarith only [h1193, h1298, h2, hlam]
        · linarith only [h1193, h1194, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1333 | h1333
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
          · linarith only [h0, h1334, h2, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
            · linarith only [h0, h1336, h994, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1338 | h1338
              · linarith only [h0, h1338, h994, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1340 | h1340
                · linarith only [h1, h1193, h1333, h1340, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1342 | h1342
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1343 | h1343
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1344 | h1344
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1345 | h1345
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1346 | h1346
                          · rcases h2bigk with h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h994, hc12, hlam, hphi, ht23, ht34, ht45, p1347_1, u5elo2]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h2, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h910, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h994, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h0, hlam, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1334, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1336, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1338, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1, h1193, h1342, h1343, h1346, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h0, h994, hc12, hc23, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1343, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h0, h1343, h994, hc12, hc23, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1347_1, u5elo2]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1344, hlam, p1347_0]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [h1345, hlam, p1347_1]
                            · have p1347_0 := h1347c.1
                              have p1347_1 := h1347c.2.1
                              have p1347_2 := h1347c.2.2.1
                              have p1347_3 := h1347c.2.2.2
                              linarith only [hlam, p1347_0]
                          · linarith only [h1193, h1346, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h1345, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h1, h1193, h1342, h1344, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1376 | h1376
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1377 | h1377
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1378 | h1378
                          · rcases h2bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h994, hc12, hc25, hlam, hphi, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h2, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h910, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h994, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h0, hlam, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1334, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1336, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1338, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, hc02, hc34, hlam, hphi, ht23, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, hc12, hc34, hlam, hphi, ht23, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, hlam, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h0, h1343, hc12, hc34, hlam, hphi, ht23, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, hc12, hc34, hlam, hphi, ht23, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1343, h2, hc03, hc34, hlam, hphi, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h0, h1343, h994, hc12, hc34, hlam, hphi, ht23, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h0, h1376, hc12, hc23, hlam, hphi, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1379_1, u5elo2]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1376, hlam, p1379_0]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [h1377, hlam, p1379_1]
                            · have p1379_0 := h1379c.1
                              have p1379_1 := h1379c.2.1
                              have p1379_2 := h1379c.2.2.1
                              have p1379_3 := h1379c.2.2.2
                              linarith only [hlam, p1379_0]
                          · linarith only [h1, h1342, h1343, h1378, h2, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1377, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1, h1342, h1376, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1193, h1333, h1342, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
          · linarith only [h0, h1409, h2, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1411 | h1411
            · linarith only [h0, h1411, h910, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1413 | h1413
              · linarith only [h1, h1333, h1409, h1413, h994, hc05, hlam, hphi, u5elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1415 | h1415
                · linarith only [h1, h1333, h1415, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1417 | h1417
                  · linarith only [h1, h1333, h1417, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1419 | h1419
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1420 | h1420
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1421 | h1421
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1422 | h1422
                          · rcases h2bigk with h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1333, h1420, h2, hc12, hlam, hphi, ht23, ht34, ht45, p1423_1, u5elo2]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h2, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h910, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h994, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1409, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1411, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1413, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, h1333, h1420, h1421, h2, hc12, hc23, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, h1333, h1420, h2, hc12, hc23, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1419, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, h1333, h1419, h1420, h2, hc12, hc23, hlam, hphi, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1423_1, u5elo2]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1423_1, u5elo2]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1420, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1421, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                          · linarith only [h1193, h1422, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h0, h1421, h910, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1420, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1452 | h1452
                      · linarith only [h0, h1333, h1419, h1452, h2, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1452, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2

end R2N4
