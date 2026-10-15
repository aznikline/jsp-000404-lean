import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3432000 in
theorem r1l7_11_13_25_L_0_L_R_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h991 | h991
  · rcases m.htr 0 2 5 (by decide) (by decide) with h992 | h992
    · rcases m.htr 0 3 5 (by decide) (by decide) with h993 | h993
      · rcases m.htr 0 4 5 (by decide) (by decide) with h994 | h994
        · rcases m.htr 1 2 5 (by decide) (by decide) with h995 | h995
          · rcases m.htr 1 3 4 (by decide) (by decide) with h996 | h996
            · rcases m.htr 1 3 5 (by decide) (by decide) with h997 | h997
              · rcases m.htr 1 4 5 (by decide) (by decide) with h998 | h998
                · rcases m.htr 2 3 4 (by decide) (by decide) with h999 | h999
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1000 | h1000
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1001 | h1001
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1002 | h1002
                        · rcases h5bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h0, hlam, p1003_1]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h1000, h994, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1, u3ehi4]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h992, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1, u3ehi4]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h0, h996, h998, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1, u1elo2]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h996, h998, hc05, hlam, hphi, ht01, ht0b, ht5b, p1003_1, u1elo2]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h1000, h996, h998, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u1elo2, u3ehi4]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h996, h998, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1003_1, u1elo2, u3ehi4]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h996, h998, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1, u1elo2]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h992, hlam, p1003_1]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h995, hlam, p1003_1]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h992, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1003_1, u3ehi4]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h995, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1, u1elo1]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h993, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h997, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h1000, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h993, hc03, hc45, hlam, hphi, ht0b, ht5b, p1003_1]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h994, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h998, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h1001, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [h1002, hlam, p1003_0]
                          · have p1003_0 := h1003c.1
                            have p1003_1 := h1003c.2.1
                            have p1003_2 := h1003c.2.2.1
                            have p1003_3 := h1003c.2.2.2
                            linarith only [hlam, p1003_0]
                        · linarith only [h1002, h996, h998, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                      · linarith only [h1001, h996, h998, h999, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h1000, h999, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h996, h999, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · linarith only [h0, h994, h998, hlam]
              · linarith only [h996, h997, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
              · linarith only [h1035, h996, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1035, h993, hlam]
          · linarith only [h0, h992, h995, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1039 | h1039
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1040 | h1040
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1041 | h1041
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1042 | h1042
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1043 | h1043
                  · linarith only [h1040, h1042, h1043, h991, h994, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                  · linarith only [h1040, h1043, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1046 | h1046
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
                      · linarith only [h1048, h991, h994, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1050 | h1050
                        · linarith only [h1046, h1050, h991, h994, hlam]
                        · rcases h5bigk with h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c | h1052c
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h0, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p1052_1, u1elo4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1052_1, u1elo4, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h994, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1052_1, u1elo4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1039, h1047, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1052_1, u1elo1, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1039, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1052_1, u1elo1, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1042, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h992, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1039, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1052_1, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1048, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h993, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1041, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1047, hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1050, hlam, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1046, h991, h994, hc34, hc45, hlam, hphi, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1052_1]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [h1047, hc45, hlam, hphi, ht34, p1052_1, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1052_1, u3ehi4]
                          · have p1052_0 := h1052c.1
                            have p1052_1 := h1052c.2.1
                            have p1052_2 := h1052c.2.2.1
                            have p1052_3 := h1052c.2.2.2
                            linarith only [hlam, p1052_0]
                    · linarith only [h1046, h1047, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1040, h1046, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · linarith only [h1040, h1041, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1081 | h1081
              · linarith only [h1040, h1081, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1081, h993, hlam]
          · linarith only [h0, h1039, h992, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1086 | h1086
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1087 | h1087
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1088 | h1088
              · linarith only [h1088, h993, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1087, h1088, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
              · linarith only [h1087, h1091, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1093 | h1093
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1094 | h1094
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1095 | h1095
                    · linarith only [h1095, h992, h993, hlam]
                    · linarith only [h1094, h1095, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1098 | h1098
                    · linarith only [h1094, h1098, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1100 | h1100
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1101 | h1101
                        · rcases h5bigk with h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c | h1102c
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h0, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1098, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1102_1, u3ehi2]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h993, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo4]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo4]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1086, h1098, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1102_1, u1elo1, u3ehi2]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1091, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo4]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h992, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1086, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1098, hlam, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h0, h1086, h992, hc45, hlam, hphi, ht01, ht0b, ht5b, p1102_1, u1elo1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1102_1]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1098, hc35, hlam, hphi, p1102_1, u3ehi2]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            rcases p1102_3 (m.d 0 5) (by simp) with h1122 | h1122
                            · linarith only [h1122, h993, hlam]
                            · linarith only [h1085, h1122, hlam]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1085, hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1093, hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1100, hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [h1101, hlam, p1102_0]
                          · have p1102_0 := h1102c.1
                            have p1102_1 := h1102c.2.1
                            have p1102_2 := h1102c.2.2.1
                            have p1102_3 := h1102c.2.2.2
                            linarith only [hlam, p1102_0]
                        · linarith only [h0, h1085, h1086, h1087, h1101, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                      · linarith only [h1093, h1094, h1100, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
                · linarith only [h0, h1085, h1093, hlam]
          · linarith only [h0, h1086, h992, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1136 | h1136
              · linarith only [h1136, h993, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1135, h1136, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1139 | h1139
              · linarith only [h1135, h1139, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1141 | h1141
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1142 | h1142
                  · linarith only [h1085, h1135, h1141, h1142, h991, hlam]
                  · linarith only [h1085, h1141, h1142, h991, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                  · linarith only [h1085, h1135, h1145, h991, hc45, hlam, hphi, ht34, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1147 | h1147
                    · linarith only [h1145, h1147, h993, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1149 | h1149
                      · linarith only [h1085, h1149, h991, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1151 | h1151
                        · linarith only [h1085, h1145, h1151, h991, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1135, h1151, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1134, h992, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1155 | h1155
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1156 | h1156
        · linarith only [h1156, h991, h992, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1158 | h1158
          · linarith only [h1158, h991, h992, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1161 | h1161
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1162 | h1162
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1163 | h1163
                  · linarith only [h1156, h1160, h1162, h1163, h991, h992, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                  · linarith only [h1160, h1163, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1166 | h1166
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1168 | h1168
                      · linarith only [h0, h1162, h1168, h991, h992, hlam]
                      · linarith only [h1166, h1168, h991, h992, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h1161, h1167, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                  · linarith only [h1160, h1166, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · linarith only [h1160, h1161, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1174 | h1174
              · linarith only [h1160, h1174, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1155, h1174, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1177 | h1177
        · linarith only [h1177, h991, h992, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1179 | h1179
          · linarith only [h1179, h991, h992, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1182 | h1182
              · linarith only [h1155, h1182, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1181, h1182, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1185 | h1185
              · linarith only [h1181, h1185, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1188 | h1188
                  · linarith only [h1155, h1177, h1181, h1187, h1188, h991, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1177, h1187, h1188, h991, h992, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                  · linarith only [h0, h1181, h1191, h991, h992, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1193 | h1193
                    · linarith only [h1191, h1193, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1191, h1193, h991, h992, hc35, hlam, hphi, u3ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1196 | h1196
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1197 | h1197
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1201 | h1201
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1203 | h1203
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1206 | h1206
                        · rcases h5bigk with h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c | h1207c
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h0, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1204, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi4]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1196, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi4]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1196, h1203, h991, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1202, hc05, hlam, hphi, ht01, ht0b, ht5b, p1207_1, u1elo3]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1202, h1204, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1207_1, u1elo3, u3ehi4]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1200, h1202, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1207_1, u1elo2, u3ehi4]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1200, h1202, hc45, hlam, hphi, ht01, ht0b, ht5b, p1207_1, u1elo2]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1196, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1199, hlam, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1196, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1207_1, u3ehi4]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1196, h1203, h991, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1197, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1201, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1204, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1197, hc03, hc45, hlam, hphi, ht0b, ht5b, p1207_1]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1198, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1202, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1205, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [h1206, hlam, p1207_0]
                          · have p1207_0 := h1207c.1
                            have p1207_1 := h1207c.2.1
                            have p1207_2 := h1207c.2.2.1
                            have p1207_3 := h1207c.2.2.2
                            linarith only [hlam, p1207_0]
                        · linarith only [h1200, h1202, h1206, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                      · linarith only [h1200, h1202, h1205, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1196, h1197, h1203, h1204, h991, hlam]
                  · linarith only [h1200, h1203, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · linarith only [h0, h1198, h1202, hlam]
              · linarith only [h0, h1197, h1199, h1200, h1201, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1239 | h1239
              · linarith only [h1200, h1239, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1197, h1239, hlam]
          · linarith only [h1196, h1199, h991, hc12, hc24, hlam, hphi]
        · linarith only [h1196, h1198, h991, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1245 | h1245
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1246 | h1246
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1247 | h1247
              · linarith only [h1197, h1247, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1246, h1247, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1250 | h1250
              · linarith only [h1246, h1250, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1252 | h1252
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1253 | h1253
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1254 | h1254
                    · linarith only [h1196, h1250, h1253, h1254, h991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1253, h1254, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1257 | h1257
                    · linarith only [h1253, h1257, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1196, h1253, h1257, h991, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h1244, h1252, hlam]
          · linarith only [h1196, h1245, h991, hc12, hc24, hlam, hphi]
        · linarith only [h1196, h1244, h991, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1264 | h1264
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1265 | h1265
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1266 | h1266
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1267 | h1267
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1268 | h1268
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1269 | h1269
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1270 | h1270
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1271 | h1271
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1272 | h1272
                        · rcases h5bigk with h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h0, hlam, p1273_1]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1196, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1264, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1273_1, u3ehi4]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1196, h1265, hc45, hlam, hphi, ht01, ht0b, ht5b, p1273_1, u1elo1]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1268, hc05, hlam, hphi, ht01, ht0b, ht5b, p1273_1, u1elo3]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1196, h1268, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1273_1, u1elo3]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1266, h1268, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1273_1, u1elo2, u3ehi4]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1266, h1268, hc45, hlam, hphi, ht01, ht0b, ht5b, p1273_1, u1elo2]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1273_1, u3ehi4]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1265, hlam, p1273_1]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1265, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1273_1, u1elo1, u3ehi4]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1265, hc45, hlam, hphi, ht01, ht0b, ht5b, p1273_1, u1elo1]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1263, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1267, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1270, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1263, hc03, hc45, hlam, hphi, ht0b, ht5b, p1273_1]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1264, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1268, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1271, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [h1272, hlam, p1273_0]
                          · have p1273_0 := h1273c.1
                            have p1273_1 := h1273c.2.1
                            have p1273_2 := h1273c.2.2.1
                            have p1273_3 := h1273c.2.2.2
                            linarith only [hlam, p1273_0]
                        · linarith only [h1196, h1264, h1265, h1272, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                      · linarith only [h1196, h1264, h1265, h1271, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h1196, h1263, h1265, h1270, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                  · linarith only [h1266, h1269, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · linarith only [h1196, h1264, h1265, h1266, h1268, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
              · linarith only [h1196, h1263, h1265, h1267, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
              · linarith only [h1266, h1305, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1196, h1263, h1265, h1305, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1309 | h1309
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1311 | h1311
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1312 | h1312
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1313 | h1313
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1314 | h1314
                        · rcases h5bigk with h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h0, hlam, p1315_1]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1196, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h0, h1308, h1310, hc35, hlam, hphi, ht01, ht0b, ht5b, p1315_1, u1elo2]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h0, h1308, h1310, hc45, hlam, hphi, ht01, ht0b, ht5b, p1315_1, u1elo2]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1308, h1310, hc05, hlam, hphi, ht01, ht0b, ht5b, p1315_1, u1elo2]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1265, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1308, h1310, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1315_1, u1elo2, u3ehi4]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1308, h1310, hc45, hlam, hphi, ht01, ht0b, ht5b, p1315_1, u1elo2]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1263, h1311, h1313, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1315_1, u3ehi4]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1265, h1311, h1313, hc12, hc23, hlam, hphi, p1315_1]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1311, h1313, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1315_1, u3ehi4]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            rcases p1315_3 (m.d 0 5) (by simp) with h1330 | h1330
                            · linarith only [h1196, h1330, hlam]
                            · linarith only [h1264, h1330, hlam]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1263, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1309, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1312, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h0, h1263, hc45, hlam, hphi, ht01, ht0b, ht5b, p1315_1, u1elo4]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1264, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1310, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1313, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [h1314, hlam, p1315_0]
                          · have p1315_0 := h1315c.1
                            have p1315_1 := h1315c.2.1
                            have p1315_2 := h1315c.2.2.1
                            have p1315_3 := h1315c.2.2.2
                            linarith only [hlam, p1315_0]
                        · linarith only [h1308, h1310, h1314, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                      · linarith only [h1308, h1310, h1313, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1309, h1312, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                  · linarith only [h1308, h1311, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · linarith only [h0, h1264, h1310, hlam]
              · linarith only [h1308, h1309, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1349 | h1349
              · linarith only [h1308, h1349, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1263, h1349, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1353 | h1353
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1354 | h1354
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1355 | h1355
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1356 | h1356
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1357 | h1357
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1358 | h1358
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1359 | h1359
                        · linarith only [h1264, h1353, h1359, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h1353, h1355, h1359, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                      · linarith only [h1353, h1355, h1358, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1263, h1264, h1353, h1355, h1357, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                  · linarith only [h1353, h1356, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1367 | h1367
                      · linarith only [h1352, h1353, h1355, h1367, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1369 | h1369
                        · linarith only [h1353, h1367, h1369, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                        · rcases h5bigk with h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h0, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1196, hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1196, h1352, hc35, hlam, hphi, ht01, ht0b, ht5b, p1371_1, u1elo1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1264, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1371_1, u1elo4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1352, hc25, hlam, hphi, ht01, ht0b, ht5b, p1371_1, u1elo1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1352, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u1elo1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1355, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1371_1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1352, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1352, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u1elo1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1367, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1263, hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1354, hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1366, hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hlam, p1371_0]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1369, hlam, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1263, hc45, hlam, hphi, ht34, p1371_1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1371_1]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [h1196, h1263, hc45, hlam, hphi, ht34, p1371_1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p1371_1, u3ehi4]
                          · have p1371_0 := h1371c.1
                            have p1371_1 := h1371c.2.1
                            have p1371_2 := h1371c.2.2.1
                            have p1371_3 := h1371c.2.2.2
                            linarith only [hlam, p1371_0]
                    · linarith only [h1196, h1263, h1352, h1366, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
                  · linarith only [h1353, h1365, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · linarith only [h1196, h1263, h1352, h1354, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1400 | h1400
              · linarith only [h1353, h1400, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1196, h1263, h1352, h1400, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1403 | h1403
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1404 | h1404
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1405 | h1405
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1406 | h1406
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1407 | h1407
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1408 | h1408
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1409 | h1409
                        · linarith only [h1263, h1264, h1403, h1409, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi4]
                        · linarith only [h1403, h1405, h1409, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                      · linarith only [h1403, h1405, h1408, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1406, h1407, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1403, h1406, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1415 | h1415
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1417 | h1417
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1418 | h1418
                        · linarith only [h1403, h1405, h1418, hlam]
                        · rcases h5bigk with h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h0, hlam, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1196, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1420_1, u1elo4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1264, hlam, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1420_1, u1elo4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1352, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1405, h1415, h1417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1420_1, u3ehi4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1405, hlam, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1420_1, u3ehi4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1416, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1420_1, u3ehi4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1405, h1415, h1417, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1263, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1404, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1416, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1418, hlam, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1263, hc45, hlam, hphi, ht34, p1420_1, u3ehi4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1420_1]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1417, hlam, p1420_0]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [h1415, h1417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1420_1, u3ehi4]
                          · have p1420_0 := h1420c.1
                            have p1420_1 := h1420c.2.1
                            have p1420_2 := h1420c.2.2.1
                            have p1420_3 := h1420c.2.2.2
                            linarith only [hlam, p1420_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1446 | h1446
                        · linarith only [h1403, h1405, h1446, hlam]
                        · rcases h5bigk with h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h0, hlam, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1196, hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1446, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1264, hlam, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1448_1, u1elo4]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1352, hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1446, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1448_1, u1elo4, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1405, hlam, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1263, h1446, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h0, h1417, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1417, h1446, hc45, hlam, hphi, ht34, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1417, hlam, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1263, hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1404, hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1416, hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hlam, p1448_0]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1446, hlam, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1263, h1446, hc45, hlam, hphi, ht34, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h0, h1263, h1446, hc45, hlam, hphi, ht34, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1196, hc02, hc45, hlam, hphi, ht23, ht34, p1448_1]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [h1446, hc45, hlam, hphi, ht34, p1448_1, u3ehi3]
                          · have p1448_0 := h1448c.1
                            have p1448_1 := h1448c.2.1
                            have p1448_2 := h1448c.2.2.1
                            have p1448_3 := h1448c.2.2.2
                            linarith only [hlam, p1448_0]
                    · linarith only [h1404, h1416, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                  · linarith only [h1403, h1415, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · linarith only [h0, h1263, h1403, h1404, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1477 | h1477
              · linarith only [h1403, h1477, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1263, h1477, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1480 | h1480
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1483 | h1483
              · linarith only [h1263, h1483, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1482, h1483, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1486 | h1486
              · linarith only [h1482, h1486, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1489 | h1489
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1490 | h1490
                    · linarith only [h1481, h1486, h1490, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                    · linarith only [h1489, h1490, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1493 | h1493
                    · linarith only [h1489, h1493, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1495 | h1495
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1496 | h1496
                        · rcases h5bigk with h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c | h1497c
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h0, hlam, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1196, hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1263, hlam, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1196, h1481, hc45, hlam, hphi, ht01, ht0b, ht5b, p1497_1, u1elo1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1263, h1488, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1497_1, u1elo3, u3ehi0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1488, hc25, hlam, hphi, ht01, ht0b, ht5b, p1497_1, u1elo3]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1486, hlam, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1497_1, u1elo4]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1497_1, u3ehi0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1481, hlam, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1493, hlam, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1481, hc45, hlam, hphi, ht01, ht0b, ht5b, p1497_1, u1elo1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1263, hc35, hlam, hphi, p1497_1, u3ehi0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1497_1]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1196, h1263, hc35, hlam, hphi, p1497_1, u3ehi0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            rcases p1497_3 (m.d 0 5) (by simp) with h1517 | h1517
                            · linarith only [h1263, h1517, hlam]
                            · linarith only [h1480, h1517, hlam]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1480, hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1488, hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1495, hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [h1496, hlam, p1497_0]
                          · have p1497_0 := h1497c.1
                            have p1497_1 := h1497c.2.1
                            have p1497_2 := h1497c.2.2.1
                            have p1497_3 := h1497c.2.2.2
                            linarith only [hlam, p1497_0]
                        · linarith only [h1196, h1480, h1481, h1496, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                      · linarith only [h1480, h1495, h991, hlam]
                · linarith only [h1196, h1480, h1481, h1482, h1488, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1528 | h1528
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1529 | h1529
              · linarith only [h1263, h1529, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1528, h1529, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1532 | h1532
              · linarith only [h1528, h1532, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1534 | h1534
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1535 | h1535
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1536 | h1536
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1537 | h1537
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1538 | h1538
                        · rcases h5bigk with h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h0, hlam, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1196, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1263, hlam, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1539_1, u1elo4]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1539_1, u1elo4]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1481, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1532, hlam, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1528, h1534, h1535, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1539_1, u3ehi0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1532, h1536, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1539_1, u3ehi1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            rcases p1539_3 (m.d 0 5) (by simp) with h1554 | h1554
                            · linarith only [h1196, h1554, hlam]
                            · linarith only [h1480, h1554, hlam]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1263, hc35, hlam, hphi, p1539_1, u3ehi0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1536, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1535, h1538, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1539_1]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1480, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1534, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1537, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [h1538, hlam, p1539_0]
                          · have p1539_0 := h1539c.1
                            have p1539_1 := h1539c.2.1
                            have p1539_2 := h1539c.2.2.1
                            have p1539_3 := h1539c.2.2.2
                            linarith only [hlam, p1539_0]
                        · linarith only [h1480, h1528, h1535, h1538, h991, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1528, h1534, h1535, h1537, hlam]
                    · linarith only [h1535, h1536, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1570 | h1570
                    · linarith only [h1535, h1570, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1572 | h1572
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1573 | h1573
                        · rcases h5bigk with h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h0, hlam, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1196, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1263, hlam, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1574_1, u1elo4]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1574_1, u1elo4]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1481, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1532, hlam, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1534, hc45, hlam, hphi, ht01, ht0b, ht5b, p1574_1, u1elo3]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1574_1, u3ehi0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h0, h1570, hc01, hc35, hlam, hphi, ht12, ht23, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1570, hlam, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            rcases p1574_3 (m.d 0 5) (by simp) with h1589 | h1589
                            · linarith only [h1196, h1589, hlam]
                            · linarith only [h1480, h1589, hlam]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1263, h1573, hc34, hlam, hphi, p1574_1, u3ehi0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h0, h1573, hc01, hc34, hlam, hphi, ht12, ht23, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1196, h1573, hc02, hc34, hlam, hphi, ht23, p1574_1]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            rcases p1574_3 (m.d 0 5) (by simp) with h1596 | h1596
                            · linarith only [h1263, h1596, hlam]
                            · linarith only [h1480, h1596, hlam]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1480, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1534, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1572, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [h1573, hlam, p1574_0]
                          · have p1574_0 := h1574c.1
                            have p1574_1 := h1574c.2.1
                            have p1574_2 := h1574c.2.2.1
                            have p1574_3 := h1574c.2.2.2
                            linarith only [hlam, p1574_0]
                        · linarith only [h1480, h1535, h1573, h991, hlam]
                      · linarith only [h1480, h1572, h991, hlam]
                · linarith only [h0, h1480, h1534, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1607 | h1607
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1608 | h1608
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1609 | h1609
              · linarith only [h1263, h1609, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1608, h1609, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1612 | h1612
              · linarith only [h1608, h1612, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1614 | h1614
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1615 | h1615
                  · linarith only [h1480, h1608, h1614, h1615, h991, hc02, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1617 | h1617
                    · linarith only [h1612, h1615, h1617, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1619 | h1619
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1620 | h1620
                        · rcases h5bigk with h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c | h1621c
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h0, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1196, hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1263, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1480, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1621_1, u1elo4]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1480, h1607, h1619, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1621_1, u1elo1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1612, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1480, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1621_1, u1elo4]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1621_1, u3ehi0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1607, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1617, hlam, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1480, h1607, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1621_1, u1elo1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1263, hc35, hlam, hphi, p1621_1, u3ehi0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1196, h1263, hc35, hlam, hphi, p1621_1, u3ehi0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1480, h1620, h991, hc02, hc34, hlam, hphi, ht23, p1621_1]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1263, h1607, h1619, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1621_1, u1elo1, u3ehi0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1614, hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1619, hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [h1620, hlam, p1621_0]
                          · have p1621_0 := h1621c.1
                            have p1621_1 := h1621c.2.1
                            have p1621_2 := h1621c.2.2.1
                            have p1621_3 := h1621c.2.2.2
                            linarith only [hlam, p1621_0]
                        · linarith only [h1607, h1619, h1620, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                      · linarith only [h1614, h1619, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1649 | h1649
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1650 | h1650
                    · linarith only [h1263, h1607, h1650, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi0]
                    · linarith only [h1608, h1649, h1650, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1653 | h1653
                    · linarith only [h1649, h1653, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1655 | h1655
                      · linarith only [h1608, h1614, h1649, h1655, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1657 | h1657
                        · linarith only [h1608, h1614, h1657, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1608, h1657, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1660 | h1660
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1661 | h1661
              · linarith only [h1263, h1661, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
              · linarith only [h1660, h1661, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1664 | h1664
              · linarith only [h1660, h1664, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1666 | h1666
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1667 | h1667
                  · linarith only [h1480, h1660, h1666, h1667, h991, hc02, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1669 | h1669
                    · linarith only [h1664, h1667, h1669, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1671 | h1671
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1672 | h1672
                        · rcases h5bigk with h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h0, hlam, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1196, hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1263, hlam, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1480, hlam, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1263, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1673_1, u1elo4, u3ehi0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1607, hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1664, hlam, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1480, h1666, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1673_1, u1elo3]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1263, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1673_1, u3ehi0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1669, hlam, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1480, h991, hc02, hc25, hlam, hphi, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1263, hc35, hlam, hphi, p1673_1, u3ehi0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h0, h1480, h1666, h991, hc01, hc02, hc35, hlam, hphi, ht23, p1673_1, u1elo3]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1196, hc02, hc35, hlam, hphi, ht23, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1480, h1672, h991, hc02, hc34, hlam, hphi, ht23, p1673_1]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1263, h1666, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1673_1, u1elo3, u3ehi0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1666, hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1671, hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [h1672, hlam, p1673_0]
                          · have p1673_0 := h1673c.1
                            have p1673_1 := h1673c.2.1
                            have p1673_2 := h1673c.2.2.1
                            have p1673_3 := h1673c.2.2.2
                            linarith only [hlam, p1673_0]
                        · linarith only [h1666, h1672, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi3]
                      · linarith only [h1666, h1671, h991, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1701 | h1701
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1702 | h1702
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1703 | h1703
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1704 | h1704
                        · linarith only [h1660, h1666, h1704, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1660, h1703, h1704, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1660, h1701, h1703, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1660, h1701, h1702, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1709 | h1709
                    · linarith only [h1701, h1709, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1711 | h1711
                      · linarith only [h1660, h1666, h1701, h1711, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1713 | h1713
                        · linarith only [h1660, h1666, h1713, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1660, h1713, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 3432000 in
theorem r1l7_11_13_25_L_0_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_0_L_R_H_I_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_0_L_R_H_I_x1 m hb1 hb3 hb5 h0

end R2N4
