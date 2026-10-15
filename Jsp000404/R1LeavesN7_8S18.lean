import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12890 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h12963 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 1 2 3 (by decide) (by decide) with h12964 | h12964
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12965 | h12965
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12966 | h12966
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12967 | h12967
        · rcases m.htr 1 3 5 (by decide) (by decide) with h12968 | h12968
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12969 | h12969
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12970 | h12970
              · linarith only [h12890, h12963, h12970, h9886, h9889, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12972 | h12972
                · linarith only [h12964, h12967, h12972, h9886, h9889, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12974 | h12974
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12975 | h12975
                    · rcases h0bigk with h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c | h12976c
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h0, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h7600, hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h8836, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h9666, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        rcases p12976_3 (m.d 0 1) (by simp) with h12982 | h12982
                        · linarith only [h0, h12982, hlam]
                        · rcases p12976_3 (m.d 0 2) (by simp) with h12984 | h12984
                          · rcases p12976_3 (m.d 0 3) (by simp) with h12985 | h12985
                            · linarith only [h12985, h9886, hlam]
                            · linarith only [h12985, h7600, hlam]
                          · linarith only [h0, h12984, hlam]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        rcases p12976_3 (m.d 0 1) (by simp) with h12990 | h12990
                        · linarith only [h0, h12990, hlam]
                        · rcases p12976_3 (m.d 0 2) (by simp) with h12992 | h12992
                          · rcases p12976_3 (m.d 0 3) (by simp) with h12993 | h12993
                            · linarith only [h12993, h9886, hlam]
                            · rcases p12976_3 (m.d 0 4) (by simp) with h12995 | h12995
                              · linarith only [h12995, h9887, hlam]
                              · linarith only [h12995, h9889, hlam]
                          · linarith only [h12992, h9886, hlam]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h0, h12974, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p12976_1, u5ehi4]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        rcases p12976_3 (m.d 0 1) (by simp) with h13000 | h13000
                        · linarith only [h0, h13000, hlam]
                        · rcases p12976_3 (m.d 0 2) (by simp) with h13002 | h13002
                          · rcases p12976_3 (m.d 0 3) (by simp) with h13003 | h13003
                            · linarith only [h13003, h9886, hlam]
                            · rcases p12976_3 (m.d 0 4) (by simp) with h13005 | h13005
                              · linarith only [h13005, h9887, hlam]
                              · linarith only [h12963, h13005, hlam]
                          · linarith only [h13002, h9888, hlam]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12890, h12964, h12967, h12975, hc01, hc12, hlam, hphi, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h9886, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h9889, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12890, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12964, h12967, h9889, hc01, hc12, hlam, hphi, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h9887, hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12964, h12967, h7600, h9889, hc01, hc12, hlam, hphi, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [hlam, p12976_0]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12964, h12967, h9888, h9889, hc12, hlam, hphi, ht01, ht0b, ht5b, p12976_1, u5ehi2]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12890, h12964, h12967, h12975, hc01, hc12, hlam, hphi, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h9888, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12890, h12964, h12967, h12975, h7600, hc01, hc12, hlam, hphi, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [h12963, hlam, p12976_1]
                      · have p12976_0 := h12976c.1
                        have p12976_1 := h12976c.2.1
                        have p12976_2 := h12976c.2.2.1
                        have p12976_3 := h12976c.2.2.2
                        linarith only [hlam, p12976_0]
                    · linarith only [h0, h12974, h12975, h8836, h9887, h9889, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13025 | h13025
                    · rcases h0bigk with h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h0, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h7600, hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h8836, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9666, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        rcases p13026_3 (m.d 0 1) (by simp) with h13032 | h13032
                        · linarith only [h0, h13032, hlam]
                        · rcases p13026_3 (m.d 0 2) (by simp) with h13034 | h13034
                          · rcases p13026_3 (m.d 0 3) (by simp) with h13035 | h13035
                            · linarith only [h13035, h9886, hlam]
                            · linarith only [h13035, h7600, hlam]
                          · linarith only [h0, h13034, hlam]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        rcases p13026_3 (m.d 0 1) (by simp) with h13040 | h13040
                        · linarith only [h0, h13040, hlam]
                        · rcases p13026_3 (m.d 0 2) (by simp) with h13042 | h13042
                          · rcases p13026_3 (m.d 0 3) (by simp) with h13043 | h13043
                            · linarith only [h13043, h9886, hlam]
                            · rcases p13026_3 (m.d 0 4) (by simp) with h13045 | h13045
                              · linarith only [h13045, h9887, hlam]
                              · linarith only [h13045, h9889, hlam]
                          · linarith only [h13042, h9886, hlam]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h0, h12963, h12970, h12974, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        rcases p13026_3 (m.d 0 1) (by simp) with h13050 | h13050
                        · linarith only [h0, h13050, hlam]
                        · rcases p13026_3 (m.d 0 2) (by simp) with h13052 | h13052
                          · rcases p13026_3 (m.d 0 3) (by simp) with h13053 | h13053
                            · linarith only [h13053, h9886, hlam]
                            · rcases p13026_3 (m.d 0 4) (by simp) with h13055 | h13055
                              · linarith only [h13055, h9887, hlam]
                              · linarith only [h12963, h13055, hlam]
                          · linarith only [h13052, h9888, hlam]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9889, hc01, hc34, hlam, hphi, ht12, ht23, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9886, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9889, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12890, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12964, h12967, h9889, hc01, hc12, hlam, hphi, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9887, hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12964, h12967, h7600, h9889, hc01, hc12, hlam, hphi, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [hlam, p13026_0]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12963, h12964, h12967, h12970, h12974, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12890, h12964, h12967, h13025, hc01, hc12, hlam, hphi, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h9888, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12890, h12964, h12967, h13025, h7600, hc01, hc12, hlam, hphi, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [h12963, hlam, p13026_1]
                      · have p13026_0 := h13026c.1
                        have p13026_1 := h13026c.2.1
                        have p13026_2 := h13026c.2.2.1
                        have p13026_3 := h13026c.2.2.2
                        linarith only [hlam, p13026_0]
                    · linarith only [h12963, h12964, h12967, h13025, h7600, h8836, h9889, hc01, hc12, hlam, hphi]
            · linarith only [h12963, h12964, h12967, h12969, h8836, h9889, hc01, hc12, hlam, hphi]
          · linarith only [h12963, h12967, h12968, h9889, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13077 | h13077
          · linarith only [h12890, h12967, h13077, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13079 | h13079
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13080 | h13080
              · linarith only [h12967, h13080, h7600, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13082 | h13082
                · linarith only [h13077, h13082, h7600, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13084 | h13084
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13085 | h13085
                    · rcases h0bigk with h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c | h13086c
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h0, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h7600, hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h8836, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h9666, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13092 | h13092
                        · linarith only [h0, h13092, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13094 | h13094
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13095 | h13095
                            · linarith only [h13095, h9886, hlam]
                            · linarith only [h13095, h7600, hlam]
                          · linarith only [h0, h13094, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13100 | h13100
                        · linarith only [h0, h13100, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13102 | h13102
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13103 | h13103
                            · linarith only [h13103, h9886, hlam]
                            · rcases p13086_3 (m.d 0 4) (by simp) with h13105 | h13105
                              · linarith only [h13105, h9887, hlam]
                              · linarith only [h13105, h9889, hlam]
                          · linarith only [h13102, h9886, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h0, h13084, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p13086_1, u5ehi4]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13110 | h13110
                        · linarith only [h0, h13110, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13112 | h13112
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13113 | h13113
                            · linarith only [h13113, h9886, hlam]
                            · rcases p13086_3 (m.d 0 4) (by simp) with h13115 | h13115
                              · linarith only [h13115, h9887, hlam]
                              · linarith only [h12963, h13115, hlam]
                          · linarith only [h13112, h9888, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h13077, h13085, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h9886, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h9889, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h12890, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13124 | h13124
                        · linarith only [h13124, h8836, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13126 | h13126
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13127 | h13127
                            · linarith only [h13127, h9889, hlam]
                            · linarith only [h13127, h7600, hlam]
                          · linarith only [h0, h13126, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h9887, hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13132 | h13132
                        · linarith only [h13132, h8836, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13134 | h13134
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13135 | h13135
                            · linarith only [h13135, h9889, hlam]
                            · rcases p13086_3 (m.d 0 4) (by simp) with h13137 | h13137
                              · rcases p13086_3 (m.d 0 5) (by simp) with h13138 | h13138
                                · linarith only [h12963, h13138, hlam]
                                · linarith only [h12890, h13138, hlam]
                              · linarith only [h13137, h9889, hlam]
                          · linarith only [h13134, h9886, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [hlam, p13086_0]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13144 | h13144
                        · linarith only [h13144, h8836, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13146 | h13146
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13147 | h13147
                            · linarith only [h13147, h9889, hlam]
                            · rcases p13086_3 (m.d 0 4) (by simp) with h13149 | h13149
                              · rcases p13086_3 (m.d 0 5) (by simp) with h13150 | h13150
                                · linarith only [h12963, h13150, hlam]
                                · rcases h2bigk with h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c | h13152c
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h0, hlam, p13152_1]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    rcases p13152_3 (m.d 0 2) (by simp) with h13155 | h13155
                                    · rcases p13152_3 (m.d 1 2) (by simp) with h13156 | h13156
                                      · rcases p13152_3 (m.d 2 3) (by simp) with h13157 | h13157
                                        · linarith only [h13157, hlam, p13152_0]
                                        · rcases p13152_3 (m.d 2 4) (by simp) with h13159 | h13159
                                          · linarith only [h13159, h9887, hlam]
                                          · linarith only [h13080, h13159, hlam]
                                      · linarith only [h12964, h13156, hlam]
                                    · linarith only [h13155, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h0, h13084, hc12, hlam, hphi, ht01, ht0b, ht5b, p13152_1, u5ehi4]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    rcases p13152_3 (m.d 0 2) (by simp) with h13165 | h13165
                                    · rcases p13152_3 (m.d 1 2) (by simp) with h13166 | h13166
                                      · rcases p13152_3 (m.d 2 3) (by simp) with h13167 | h13167
                                        · linarith only [h13167, h9886, hlam]
                                        · rcases p13152_3 (m.d 2 4) (by simp) with h13169 | h13169
                                          · linarith only [h13169, h9887, hlam]
                                          · linarith only [h13084, h13169, hlam]
                                      · linarith only [h12966, h13166, hlam]
                                    · linarith only [h13165, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h13084, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p13152_1, u5ehi4]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    rcases p13152_3 (m.d 0 2) (by simp) with h13176 | h13176
                                    · linarith only [h0, h13176, hlam]
                                    · linarith only [h13176, h9886, hlam]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h13084, hc12, hlam, hphi, ht01, ht0b, ht5b, p13152_1, u5ehi4]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    rcases p13152_3 (m.d 0 2) (by simp) with h13180 | h13180
                                    · linarith only [h0, h13180, hlam]
                                    · linarith only [h13180, h9888, hlam]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h9886, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h12964, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h13080, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h13082, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h9887, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h12965, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    rcases p13152_3 (m.d 0 2) (by simp) with h13190 | h13190
                                    · rcases p13152_3 (m.d 1 2) (by simp) with h13191 | h13191
                                      · rcases p13152_3 (m.d 2 3) (by simp) with h13192 | h13192
                                        · linarith only [h13080, h13192, hlam]
                                        · rcases p13152_3 (m.d 2 4) (by simp) with h13194 | h13194
                                          · rcases p13152_3 (m.d 2 5) (by simp) with h13195 | h13195
                                            · linarith only [h13084, h13195, hlam]
                                            · linarith only [h13082, h13195, hlam]
                                          · linarith only [h13080, h13194, hlam]
                                      · linarith only [h12964, h13191, hlam]
                                    · linarith only [h13190, h9886, hlam]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h9887, hc02, hlam, hphi, ht0b, ht5b, p13152_1, u5ehi2]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h9888, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h12966, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h12967, h8836, h9888, hc23, hc34, hlam, hphi, p13086_1, p13152_1]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [h13084, hlam, p13152_0]
                                  · have p13152_0 := h13152c.1
                                    have p13152_1 := h13152c.2.1
                                    have p13152_2 := h13152c.2.2.1
                                    have p13152_3 := h13152c.2.2.2
                                    linarith only [hlam, p13152_0]
                              · linarith only [h12963, h13149, hlam]
                          · linarith only [h13146, h9888, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13210 | h13210
                        · linarith only [h13210, h9666, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13212 | h13212
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13213 | h13213
                            · linarith only [h12890, h13213, hlam]
                            · linarith only [h13213, h7600, hlam]
                          · linarith only [h0, h13212, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h9888, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        rcases p13086_3 (m.d 0 1) (by simp) with h13218 | h13218
                        · linarith only [h13218, h9666, hlam]
                        · rcases p13086_3 (m.d 0 2) (by simp) with h13220 | h13220
                          · rcases p13086_3 (m.d 0 3) (by simp) with h13221 | h13221
                            · linarith only [h12890, h13221, hlam]
                            · rcases p13086_3 (m.d 0 4) (by simp) with h13223 | h13223
                              · rcases p13086_3 (m.d 0 5) (by simp) with h13224 | h13224
                                · rcases h2bigk with h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c | h13225c
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h0, hlam, p13225_1]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13228 | h13228
                                    · rcases p13225_3 (m.d 1 2) (by simp) with h13229 | h13229
                                      · rcases p13225_3 (m.d 2 3) (by simp) with h13230 | h13230
                                        · linarith only [h13230, hlam, p13225_0]
                                        · rcases p13225_3 (m.d 2 4) (by simp) with h13232 | h13232
                                          · linarith only [h13232, h9887, hlam]
                                          · linarith only [h13080, h13232, hlam]
                                      · linarith only [h12964, h13229, hlam]
                                    · linarith only [h13228, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h0, h13084, hc12, hlam, hphi, ht01, ht0b, ht5b, p13225_1, u5ehi4]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13238 | h13238
                                    · rcases p13225_3 (m.d 1 2) (by simp) with h13239 | h13239
                                      · rcases p13225_3 (m.d 2 3) (by simp) with h13240 | h13240
                                        · linarith only [h13240, h9886, hlam]
                                        · rcases p13225_3 (m.d 2 4) (by simp) with h13242 | h13242
                                          · linarith only [h13242, h9887, hlam]
                                          · linarith only [h13084, h13242, hlam]
                                      · linarith only [h12966, h13239, hlam]
                                    · linarith only [h13238, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13084, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p13225_1, u5ehi4]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13249 | h13249
                                    · linarith only [h0, h13249, hlam]
                                    · linarith only [h13249, h9886, hlam]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13084, hc12, hlam, hphi, ht01, ht0b, ht5b, p13225_1, u5ehi4]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13253 | h13253
                                    · linarith only [h0, h13253, hlam]
                                    · linarith only [h13253, h9888, hlam]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h9886, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h12964, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13080, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13082, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h9887, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h12965, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13263 | h13263
                                    · rcases p13225_3 (m.d 1 2) (by simp) with h13264 | h13264
                                      · rcases p13225_3 (m.d 2 3) (by simp) with h13265 | h13265
                                        · linarith only [h13080, h13265, hlam]
                                        · rcases p13225_3 (m.d 2 4) (by simp) with h13267 | h13267
                                          · rcases p13225_3 (m.d 2 5) (by simp) with h13268 | h13268
                                            · linarith only [h13084, h13268, hlam]
                                            · linarith only [h13082, h13268, hlam]
                                          · linarith only [h13080, h13267, hlam]
                                      · linarith only [h12964, h13264, hlam]
                                    · linarith only [h13263, h9886, hlam]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13084, h9887, hc02, hlam, hphi, ht0b, ht5b, p13225_1, u5ehi4]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h9888, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h12966, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    rcases p13225_3 (m.d 0 2) (by simp) with h13278 | h13278
                                    · rcases p13225_3 (m.d 1 2) (by simp) with h13279 | h13279
                                      · rcases p13225_3 (m.d 2 3) (by simp) with h13280 | h13280
                                        · linarith only [h13082, h13280, hlam]
                                        · rcases p13225_3 (m.d 2 4) (by simp) with h13282 | h13282
                                          · rcases p13225_3 (m.d 2 5) (by simp) with h13283 | h13283
                                            · rcases h3bigk with h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c | h13284c
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h7600, hlam, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13086_1, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h9889, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h12890, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13077, h13085, hc03, hc34, hlam, hphi, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13077, h13085, hc23, hc34, hlam, hphi, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h12967, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13077, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h9886, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h12964, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13080, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13082, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                rcases p13284_3 (m.d 0 3) (by simp) with h13300 | h13300
                                                · linarith only [h13300, hlam, p13284_0]
                                                · rcases p13284_3 (m.d 1 3) (by simp) with h13302 | h13302
                                                  · linarith only [h12967, h13302, hlam]
                                                  · linarith only [h13302, h7600, hlam]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                rcases p13284_3 (m.d 0 3) (by simp) with h13306 | h13306
                                                · linarith only [h13306, h9889, hlam]
                                                · linarith only [h13306, h9886, hlam]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h0, h13077, h13084, h9666, h9887, hc01, hc12, hc23, hc34, hlam, hphi, p13225_1, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                rcases p13284_3 (m.d 0 3) (by simp) with h13311 | h13311
                                                · linarith only [h13311, hlam, p13284_0]
                                                · rcases p13284_3 (m.d 1 3) (by simp) with h13313 | h13313
                                                  · linarith only [h13077, h13313, hlam]
                                                  · linarith only [h13313, h7600, hlam]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h0, h13084, h7600, h9887, hc01, hc12, hc23, hc35, hlam, hphi, p13225_1, p13284_1]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                rcases p13284_3 (m.d 0 3) (by simp) with h13317 | h13317
                                                · linarith only [h12890, h13317, hlam]
                                                · linarith only [h13317, h9886, hlam]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [h13085, hlam, p13284_0]
                                              · have p13284_0 := h13284c.1
                                                have p13284_1 := h13284c.2.1
                                                have p13284_2 := h13284c.2.2.1
                                                have p13284_3 := h13284c.2.2.2
                                                linarith only [hlam, p13284_0]
                                            · linarith only [h13082, h13283, hlam]
                                          · linarith only [h13080, h13282, hlam]
                                      · linarith only [h12964, h13279, hlam]
                                    · linarith only [h13278, h9886, hlam]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [h13084, hlam, p13225_0]
                                  · have p13225_0 := h13225c.1
                                    have p13225_1 := h13225c.2.1
                                    have p13225_2 := h13225c.2.2.1
                                    have p13225_3 := h13225c.2.2.2
                                    linarith only [hlam, p13225_0]
                                · linarith only [h12890, h13224, hlam]
                              · linarith only [h13223, h9889, hlam]
                          · linarith only [h13220, h9886, hlam]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [h12963, hlam, p13086_1]
                      · have p13086_0 := h13086c.1
                        have p13086_1 := h13086c.2.1
                        have p13086_2 := h13086c.2.2.1
                        have p13086_3 := h13086c.2.2.2
                        linarith only [hlam, p13086_0]
                    · linarith only [h12963, h12967, h13085, h8836, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13334 | h13334
                    · rcases h0bigk with h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h0, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h7600, hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h8836, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h9666, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13341 | h13341
                        · linarith only [h0, h13341, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13343 | h13343
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13344 | h13344
                            · linarith only [h13344, h9886, hlam]
                            · linarith only [h13344, h7600, hlam]
                          · linarith only [h0, h13343, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13349 | h13349
                        · linarith only [h0, h13349, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13351 | h13351
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13352 | h13352
                            · linarith only [h13352, h9886, hlam]
                            · rcases p13335_3 (m.d 0 4) (by simp) with h13354 | h13354
                              · linarith only [h13354, h9887, hlam]
                              · linarith only [h13354, h9889, hlam]
                          · linarith only [h13351, h9886, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h12963, h13080, h13084, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13359 | h13359
                        · linarith only [h0, h13359, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13361 | h13361
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13362 | h13362
                            · linarith only [h13362, h9886, hlam]
                            · rcases p13335_3 (m.d 0 4) (by simp) with h13364 | h13364
                              · linarith only [h13364, h9887, hlam]
                              · linarith only [h12963, h13364, hlam]
                          · linarith only [h13361, h9888, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h13077, h13334, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h9886, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h9889, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h12890, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13373 | h13373
                        · linarith only [h13373, h8836, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13375 | h13375
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13376 | h13376
                            · linarith only [h13376, h9889, hlam]
                            · linarith only [h13376, h7600, hlam]
                          · linarith only [h0, h13375, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h9887, hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13381 | h13381
                        · linarith only [h13381, h8836, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13383 | h13383
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13384 | h13384
                            · linarith only [h13384, h9889, hlam]
                            · rcases p13335_3 (m.d 0 4) (by simp) with h13386 | h13386
                              · rcases p13335_3 (m.d 0 5) (by simp) with h13387 | h13387
                                · linarith only [h12963, h13387, hlam]
                                · linarith only [h12890, h13387, hlam]
                              · linarith only [h13386, h9889, hlam]
                          · linarith only [h13383, h9886, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [hlam, p13335_0]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h12963, h12967, h13080, h13084, h8836, hc23, hc34, hlam, hphi, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13394 | h13394
                        · linarith only [h13394, h9666, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13396 | h13396
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13397 | h13397
                            · linarith only [h12890, h13397, hlam]
                            · linarith only [h13397, h7600, hlam]
                          · linarith only [h0, h13396, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h9888, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        rcases p13335_3 (m.d 0 1) (by simp) with h13402 | h13402
                        · linarith only [h13402, h9666, hlam]
                        · rcases p13335_3 (m.d 0 2) (by simp) with h13404 | h13404
                          · rcases p13335_3 (m.d 0 3) (by simp) with h13405 | h13405
                            · linarith only [h12890, h13405, hlam]
                            · rcases p13335_3 (m.d 0 4) (by simp) with h13407 | h13407
                              · rcases p13335_3 (m.d 0 5) (by simp) with h13408 | h13408
                                · rcases h2bigk with h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c | h13409c
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h0, hlam, p13409_1]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13412 | h13412
                                    · rcases p13409_3 (m.d 1 2) (by simp) with h13413 | h13413
                                      · rcases p13409_3 (m.d 2 3) (by simp) with h13414 | h13414
                                        · linarith only [h13414, hlam, p13409_0]
                                        · rcases p13409_3 (m.d 2 4) (by simp) with h13416 | h13416
                                          · linarith only [h13416, h9887, hlam]
                                          · linarith only [h13080, h13416, hlam]
                                      · linarith only [h12964, h13413, hlam]
                                    · linarith only [h13412, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13421 | h13421
                                    · rcases p13409_3 (m.d 1 2) (by simp) with h13422 | h13422
                                      · rcases p13409_3 (m.d 2 3) (by simp) with h13423 | h13423
                                        · linarith only [h13423, h9886, hlam]
                                        · rcases p13409_3 (m.d 2 4) (by simp) with h13425 | h13425
                                          · linarith only [h13425, hlam, p13409_0]
                                          · rcases p13409_3 (m.d 2 5) (by simp) with h13427 | h13427
                                            · linarith only [h13427, h9888, hlam]
                                            · linarith only [h13084, h13427, hlam]
                                      · linarith only [h12965, h13422, hlam]
                                    · linarith only [h13421, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13432 | h13432
                                    · rcases p13409_3 (m.d 1 2) (by simp) with h13433 | h13433
                                      · rcases p13409_3 (m.d 2 3) (by simp) with h13434 | h13434
                                        · linarith only [h13434, h9886, hlam]
                                        · rcases p13409_3 (m.d 2 4) (by simp) with h13436 | h13436
                                          · linarith only [h13436, h9887, hlam]
                                          · rcases p13409_3 (m.d 2 5) (by simp) with h13438 | h13438
                                            · linarith only [h13438, hlam, p13409_0]
                                            · rcases h3bigk with h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c | h13440c
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h7600, hlam, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h12963, h12967, h8836, hc23, hc34, hlam, hphi, p13335_1, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h9889, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h12890, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13077, h13334, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13077, h13334, hc23, hc34, hlam, hphi, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h12967, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13077, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h9886, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h12964, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13080, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13082, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                rcases p13440_3 (m.d 0 3) (by simp) with h13456 | h13456
                                                · linarith only [h13456, hlam, p13440_0]
                                                · rcases p13440_3 (m.d 1 3) (by simp) with h13458 | h13458
                                                  · linarith only [h12967, h13458, hlam]
                                                  · linarith only [h13458, h7600, hlam]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                rcases p13440_3 (m.d 0 3) (by simp) with h13462 | h13462
                                                · linarith only [h13462, h9889, hlam]
                                                · linarith only [h13462, h9886, hlam]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h12890, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                rcases p13440_3 (m.d 0 3) (by simp) with h13467 | h13467
                                                · linarith only [h13467, hlam, p13440_0]
                                                · rcases p13440_3 (m.d 1 3) (by simp) with h13469 | h13469
                                                  · linarith only [h13077, h13469, hlam]
                                                  · linarith only [h13469, h7600, hlam]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h7600, hc01, hc35, hlam, hphi, ht12, ht23, p13440_1]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                rcases p13440_3 (m.d 0 3) (by simp) with h13473 | h13473
                                                · linarith only [h12890, h13473, hlam]
                                                · linarith only [h13473, h9886, hlam]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [h13334, hlam, p13440_0]
                                              · have p13440_0 := h13440c.1
                                                have p13440_1 := h13440c.2.1
                                                have p13440_2 := h13440c.2.2.1
                                                have p13440_3 := h13440c.2.2.2
                                                linarith only [hlam, p13440_0]
                                      · linarith only [h12966, h13433, hlam]
                                    · linarith only [h13432, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h9888, hc12, hlam, hphi, ht01, ht0b, ht5b, p13409_1, u5ehi2]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13482 | h13482
                                    · linarith only [h0, h13482, hlam]
                                    · linarith only [h13482, h9886, hlam]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13485 | h13485
                                    · linarith only [h0, h13485, hlam]
                                    · linarith only [h13485, h9887, hlam]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    rcases p13409_3 (m.d 0 2) (by simp) with h13488 | h13488
                                    · linarith only [h0, h13488, hlam]
                                    · linarith only [h13488, h9888, hlam]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h9886, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h12964, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h13080, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h13082, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h9887, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h12965, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h13084, hc23, hc45, hlam, hphi, ht34, p13409_1]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h13084, hlam, p13409_1]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h9888, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h12966, hlam, p13409_0]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h12963, h12967, h13084, h8836, hc23, hc34, hlam, hphi, p13409_1]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [h12963, h12967, h13080, h13084, h8836, hc23, hc34, hlam, hphi, p13409_1]
                                  · have p13409_0 := h13409c.1
                                    have p13409_1 := h13409c.2.1
                                    have p13409_2 := h13409c.2.2.1
                                    have p13409_3 := h13409c.2.2.2
                                    linarith only [hlam, p13409_0]
                                · linarith only [h12890, h13408, hlam]
                              · linarith only [h13407, h9889, hlam]
                          · linarith only [h13404, h9886, hlam]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [h12963, hlam, p13335_1]
                      · have p13335_0 := h13335c.1
                        have p13335_1 := h13335c.2.1
                        have p13335_2 := h13335c.2.2.1
                        have p13335_3 := h13335c.2.2.2
                        linarith only [hlam, p13335_0]
                    · linarith only [h12963, h12967, h13334, h8836, hlam]
            · linarith only [h12963, h13079, h8836, hlam]
      · linarith only [h0, h12966, h9888, hlam]
    · linarith only [h0, h12965, h9887, hlam]
  · linarith only [h0, h12964, h9886, hlam]

end R2N4
