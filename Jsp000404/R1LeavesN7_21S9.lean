import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6287 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h6934 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 3 5 (by decide) (by decide) with h6935 | h6935
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6936 | h6936
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6937 | h6937
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6938 | h6938
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6939 | h6939
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6940 | h6940
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6941 | h6941
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6942 | h6942
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6943 | h6943
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6944 | h6944
                    · rcases h2bigk with h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c | h6945c
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h0, hlam, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h4553, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6287, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6287, h6937, h6941, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        rcases p6945_3 (m.d 0 2) (by simp) with h6951 | h6951
                        · linarith only [h0, h6951, hlam]
                        · rcases p6945_3 (m.d 1 2) (by simp) with h6953 | h6953
                          · rcases p6945_3 (m.d 2 3) (by simp) with h6954 | h6954
                            · linarith only [h6937, h6954, hlam]
                            · linarith only [h4553, h6954, hlam]
                          · linarith only [h0, h6953, hlam]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h0, h6287, h6941, hc01, hc12, hlam, hphi, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6287, h6934, h6942, h6944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6287, h6934, h6937, h6941, hlam, p6945_2]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6934, h6937, h6942, h6944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6937, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6287, h6934, h6937, h6942, h6944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        rcases p6945_3 (m.d 0 2) (by simp) with h6966 | h6966
                        · linarith only [h4553, h6966, hlam]
                        · linarith only [h6934, h6966, hlam]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6934, h6938, h6942, h6944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6938, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6941, hlam, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        rcases p6945_3 (m.d 0 2) (by simp) with h6973 | h6973
                        · linarith only [h6287, h6973, hlam]
                        · linarith only [h6934, h6973, hlam]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6934, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6939, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6942, hlam, p6945_1]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [h6943, hlam, p6945_0]
                      · have p6945_0 := h6945c.1
                        have p6945_1 := h6945c.2.1
                        have p6945_2 := h6945c.2.2.1
                        have p6945_3 := h6945c.2.2.2
                        linarith only [hlam, p6945_0]
                    · linarith only [h6287, h6934, h6937, h6941, h6943, h6944, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h6287, h6936, h6943, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h6287, h6935, h6941, h6942, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6984 | h6984
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6985 | h6985
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6986 | h6986
                    · rcases h2bigk with h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c | h6987c
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h0, hlam, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h4553, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6287, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h4553, h6941, h6984, h6986, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        rcases p6987_3 (m.d 0 2) (by simp) with h6993 | h6993
                        · linarith only [h0, h6993, hlam]
                        · rcases p6987_3 (m.d 1 2) (by simp) with h6995 | h6995
                          · rcases p6987_3 (m.d 2 3) (by simp) with h6996 | h6996
                            · linarith only [h6937, h6996, hlam]
                            · linarith only [h4553, h6996, hlam]
                          · linarith only [h0, h6995, hlam]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h4553, h6934, h6941, h6984, h6986, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h4553, h6934, h6937, hlam, p6987_2]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6934, h6941, h6984, h6986, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6937, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6941, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        rcases p6987_3 (m.d 0 2) (by simp) with h7008 | h7008
                        · linarith only [h4553, h7008, hlam]
                        · linarith only [h6934, h7008, hlam]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6934, h6938, h6984, h6986, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6938, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h4553, h6934, h6938, h6984, h6986, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        rcases p6987_3 (m.d 0 2) (by simp) with h7015 | h7015
                        · linarith only [h6287, h7015, hlam]
                        · linarith only [h6934, h7015, hlam]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6934, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6939, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6984, hlam, p6987_1]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [h6985, hlam, p6987_0]
                      · have p6987_0 := h6987c.1
                        have p6987_1 := h6987c.2.1
                        have p6987_2 := h6987c.2.2.1
                        have p6987_3 := h6987c.2.2.2
                        linarith only [hlam, p6987_0]
                    · linarith only [h4553, h6936, h6941, h6986, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h6287, h6934, h6936, h6985, hlam]
                · linarith only [h4553, h6935, h6984, hlam]
            · linarith only [h6287, h6934, h6936, h6938, h6940, hlam]
          · linarith only [h4553, h6934, h6939, hc12, hc23, hlam, hphi]
        · linarith only [h4553, h6937, h6938, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7029 | h7029
        · linarith only [h6287, h6937, h7029, hc02, hc23, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7031 | h7031
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7032 | h7032
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7033 | h7033
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7034 | h7034
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7035 | h7035
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7036 | h7036
                    · rcases h2bigk with h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h0, hlam, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h4553, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h6287, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7042 | h7042
                        · rcases p7037_3 (m.d 1 2) (by simp) with h7043 | h7043
                          · rcases p7037_3 (m.d 2 3) (by simp) with h7044 | h7044
                            · rcases p7037_3 (m.d 2 4) (by simp) with h7045 | h7045
                              · rcases p7037_3 (m.d 2 5) (by simp) with h7046 | h7046
                                · linarith only [h7046, hlam, p7037_0]
                                · rcases h5bigk with h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h2858, hlam, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7034, h7036, hc45, hlam, hphi, ht0b, ht5b, p7048_1, u0elo4]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h0, h6934, h7029, h7033, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h0, h6934, h7029, h7033, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h2858, hc01, hc15, hlam, hphi, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7029, h7031, h7033, h7034, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7029, h7031, h7033, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7029, h7031, h7033, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h6934, hlam, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7031, hlam, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h0, h7029, h7033, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h0, h7029, h7033, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h6935, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h2858, hc01, hc35, hlam, hphi, ht12, ht23, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7034, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h0, h7029, h7033, h7034, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1, p7048_1]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h6936, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7032, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7035, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [h7036, hlam, p7048_0]
                                  · have p7048_0 := h7048c.1
                                    have p7048_1 := h7048c.2.1
                                    have p7048_2 := h7048c.2.2.1
                                    have p7048_3 := h7048c.2.2.2
                                    linarith only [hlam, p7048_0]
                              · linarith only [h7035, h7045, hlam]
                            · linarith only [h7034, h7044, hlam]
                          · linarith only [h7031, h7043, hlam]
                        · linarith only [h7042, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7029, h7033, hc02, hc23, hlam, hphi, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h6937, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7029, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7082 | h7082
                        · linarith only [h0, h7082, hlam]
                        · linarith only [h6934, h7082, hlam]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7085 | h7085
                        · linarith only [h7085, hlam, p7037_0]
                        · rcases p7037_3 (m.d 1 2) (by simp) with h7087 | h7087
                          · linarith only [h6937, h7087, hlam]
                          · linarith only [h0, h7087, hlam]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h6287, h6934, h7034, h7036, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7093 | h7093
                        · linarith only [h4553, h7093, hlam]
                        · linarith only [h6934, h7093, hlam]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7096 | h7096
                        · linarith only [h7096, hlam, p7037_0]
                        · rcases p7037_3 (m.d 1 2) (by simp) with h7098 | h7098
                          · linarith only [h7029, h7098, hlam]
                          · linarith only [h0, h7098, hlam]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h2858, h7031, h7033, hc01, hc23, hlam, hphi, ht12, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7033, hlam, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        rcases p7037_3 (m.d 0 2) (by simp) with h7104 | h7104
                        · linarith only [h6287, h7104, hlam]
                        · linarith only [h6934, h7104, hlam]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h6934, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7031, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7034, hlam, p7037_1]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [h7035, hlam, p7037_0]
                      · have p7037_0 := h7037c.1
                        have p7037_1 := h7037c.2.1
                        have p7037_2 := h7037c.2.2.1
                        have p7037_3 := h7037c.2.2.2
                        linarith only [hlam, p7037_0]
                    · rcases h2bigk with h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c | h7112c
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h0, hlam, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h4553, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6287, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h0, h7029, h7033, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7029, h7033, hc02, hc23, hlam, hphi, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6937, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7029, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7029, h7033, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6934, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6287, h6934, h7035, h7036, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        rcases p7112_3 (m.d 0 2) (by simp) with h7127 | h7127
                        · linarith only [h4553, h7127, hlam]
                        · linarith only [h6934, h7127, hlam]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6934, h7035, h7036, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h0, h6934, h7035, h7036, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7033, hlam, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        rcases p7112_3 (m.d 0 2) (by simp) with h7134 | h7134
                        · linarith only [h6287, h7134, hlam]
                        · linarith only [h6934, h7134, hlam]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h6934, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7031, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7034, hlam, p7112_1]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [h7035, hlam, p7112_0]
                      · have p7112_0 := h7112c.1
                        have p7112_1 := h7112c.2.1
                        have p7112_2 := h7112c.2.2.1
                        have p7112_3 := h7112c.2.2.2
                        linarith only [hlam, p7112_0]
                  · linarith only [h6287, h6936, h7035, hlam]
                · linarith only [h4553, h6935, h7034, hlam]
              · linarith only [h2858, h6937, h7031, h7033, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h2858, h6936, h7029, h7031, h7032, hlam]
          · linarith only [h0, h6934, h7031, hlam]
    · linarith only [h6287, h6934, h6936, hlam]
  · linarith only [h4553, h6934, h6935, hlam]

end R2N4
