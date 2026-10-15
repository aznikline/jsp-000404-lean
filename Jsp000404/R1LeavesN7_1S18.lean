import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8178000 in
set_option maxHeartbeats 8178000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9965 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  rcases m.htr 0 4 5 (by decide) (by decide) with h12967 | h12967
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12968 | h12968
    · linarith only [h0, h12968, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12970 | h12970
      · linarith only [h0, h12970, h7821, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12972 | h12972
        · linarith only [h0, h12972, h9029, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12974 | h12974
          · linarith only [h1, h12966, h12974, h9965, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12976 | h12976
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12977 | h12977
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12978 | h12978
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12979 | h12979
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12980 | h12980
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12981 | h12981
                      · rcases h0bigk with h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c | h12982c
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          rcases p12982_3 (m.d 0 1) (by simp) with h12984 | h12984
                          · rcases p12982_3 (m.d 0 2) (by simp) with h12985 | h12985
                            · linarith only [h0, h12985, hlam]
                            · rcases p12982_3 (m.d 0 3) (by simp) with h12987 | h12987
                              · linarith only [h1, h12987, hlam]
                              · linarith only [h12987, h4, hlam]
                          · linarith only [h0, h12984, hlam]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          rcases p12982_3 (m.d 0 1) (by simp) with h12991 | h12991
                          · rcases p12982_3 (m.d 0 2) (by simp) with h12992 | h12992
                            · linarith only [h0, h12992, hlam]
                            · rcases p12982_3 (m.d 0 3) (by simp) with h12994 | h12994
                              · linarith only [h1, h12994, hlam]
                              · rcases p12982_3 (m.d 0 4) (by simp) with h12996 | h12996
                                · linarith only [h12996, h2, hlam]
                                · linarith only [h12996, h9965, hlam]
                          · linarith only [h1, h12991, hlam]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          rcases p12982_3 (m.d 0 1) (by simp) with h13000 | h13000
                          · rcases p12982_3 (m.d 0 2) (by simp) with h13001 | h13001
                            · linarith only [h0, h13001, hlam]
                            · rcases p12982_3 (m.d 0 3) (by simp) with h13003 | h13003
                              · linarith only [h1, h13003, hlam]
                              · rcases p12982_3 (m.d 0 4) (by simp) with h13005 | h13005
                                · linarith only [h13005, h2, hlam]
                                · rcases p12982_3 (m.d 0 5) (by simp) with h13007 | h13007
                                  · linarith only [h13007, h3, hlam]
                                  · rcases h2bigk with h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c | h13009c
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12966, h12978, h9029, h9965, hc12, hc23, hlam, hphi, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h4, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h7821, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h9029, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h0, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12968, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12970, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12972, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13020 | h13020
                                      · linarith only [h13020, hlam, p13009_0]
                                      · rcases p13009_3 (m.d 1 2) (by simp) with h13022 | h13022
                                        · linarith only [h12968, h13022, hlam]
                                        · rcases p13009_3 (m.d 2 3) (by simp) with h13024 | h13024
                                          · rcases p13009_3 (m.d 2 4) (by simp) with h13025 | h13025
                                            · linarith only [h12978, h13025, hlam]
                                            · linarith only [h13025, h7821, hlam]
                                          · linarith only [h13024, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13029 | h13029
                                      · linarith only [h13029, h4, hlam]
                                      · linarith only [h0, h13029, hlam]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12966, h12978, h9029, h9965, hc02, hc23, hlam, hphi, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h9029, hc02, hc23, hlam, hphi, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13035 | h13035
                                      · linarith only [h13035, hlam, p13009_0]
                                      · rcases p13009_3 (m.d 1 2) (by simp) with h13037 | h13037
                                        · linarith only [h12970, h13037, hlam]
                                        · rcases p13009_3 (m.d 2 3) (by simp) with h13039 | h13039
                                          · rcases p13009_3 (m.d 2 4) (by simp) with h13040 | h13040
                                            · rcases p13009_3 (m.d 2 5) (by simp) with h13041 | h13041
                                              · linarith only [h12980, h13041, hlam]
                                              · linarith only [h13041, h9029, hlam]
                                            · linarith only [h13040, hlam, p13009_0]
                                          · linarith only [h13039, h4, hlam]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13046 | h13046
                                      · linarith only [h13046, h7821, hlam]
                                      · linarith only [h0, h13046, hlam]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12978, hlam, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h0, h9029, hc12, hc24, hlam, hphi, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13052 | h13052
                                      · linarith only [h13052, hlam, p13009_0]
                                      · rcases p13009_3 (m.d 1 2) (by simp) with h13054 | h13054
                                        · linarith only [h12972, h13054, hlam]
                                        · rcases p13009_3 (m.d 2 3) (by simp) with h13056 | h13056
                                          · rcases p13009_3 (m.d 2 4) (by simp) with h13057 | h13057
                                            · rcases p13009_3 (m.d 2 5) (by simp) with h13058 | h13058
                                              · rcases h3bigk with h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c | h13059c
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12976, h12981, h9965, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h4, hlam, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h9965, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12981, h9965, hc01, hc45, hlam, hphi, ht0b, ht5b, p12982_1, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h1, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12968, hlam, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12974, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h1, h12981, h9965, hc01, hc45, hlam, hphi, ht0b, ht5b, p12982_1, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  rcases p13059_3 (m.d 0 3) (by simp) with h13070 | h13070
                                                  · linarith only [h13070, h4, hlam]
                                                  · rcases p13059_3 (m.d 1 3) (by simp) with h13072 | h13072
                                                    · linarith only [h12968, h13072, hlam]
                                                    · rcases p13059_3 (m.d 2 3) (by simp) with h13074 | h13074
                                                      · rcases p13059_3 (m.d 3 4) (by simp) with h13075 | h13075
                                                        · linarith only [h12978, h13075, hlam]
                                                        · linarith only [h13075, h9965, hlam]
                                                      · linarith only [h13074, h4, hlam]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  rcases p13059_3 (m.d 0 3) (by simp) with h13079 | h13079
                                                  · linarith only [h13079, h4, hlam]
                                                  · linarith only [h1, h13079, hlam]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h0, h4, h9965, hc12, hc23, hlam, hphi, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h1, h12976, h12978, h9965, hlam, p13059_2]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h1, h12976, h12978, h12981, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12976, h12978, h12981, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13059_1]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12978, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  rcases p13059_3 (m.d 0 3) (by simp) with h13089 | h13089
                                                  · linarith only [h13089, h9965, hlam]
                                                  · linarith only [h12966, h13089, hlam]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12966, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12976, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12979, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [h12981, hlam, p13059_0]
                                                · have p13059_0 := h13059c.1
                                                  have p13059_1 := h13059c.2.1
                                                  have p13059_2 := h13059c.2.2.1
                                                  have p13059_3 := h13059c.2.2.2
                                                  linarith only [hlam, p13059_0]
                                              · linarith only [h13058, hlam, p13009_0]
                                            · linarith only [h13057, h7821, hlam]
                                          · linarith only [h13056, h4, hlam]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      rcases p13009_3 (m.d 0 2) (by simp) with h13100 | h13100
                                      · linarith only [h13100, h9029, hlam]
                                      · linarith only [h0, h13100, hlam]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12979, hlam, p13009_1]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [h12980, hlam, p13009_0]
                                    · have p13009_0 := h13009c.1
                                      have p13009_1 := h13009c.2.1
                                      have p13009_2 := h13009c.2.2.1
                                      have p13009_3 := h13009c.2.2.2
                                      linarith only [hlam, p13009_0]
                          · linarith only [h13000, h2, hlam]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          rcases p12982_3 (m.d 0 1) (by simp) with h13107 | h13107
                          · rcases p12982_3 (m.d 0 2) (by simp) with h13108 | h13108
                            · linarith only [h0, h13108, hlam]
                            · rcases p12982_3 (m.d 0 3) (by simp) with h13110 | h13110
                              · linarith only [h1, h13110, hlam]
                              · linarith only [h12966, h13110, hlam]
                          · linarith only [h13107, h3, hlam]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h4, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h7821, hlam, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h9029, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h1, hlam, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, h12978, h9965, hc12, hc23, hlam, hphi, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h9965, hlam, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, h12978, h9029, h9965, hc12, hc23, hlam, hphi, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h2, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, h12978, h9965, hc12, hc23, hlam, hphi, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h1, h12976, h12978, h12981, h9965, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, h12978, h9029, h9965, hc12, hc23, hlam, hphi, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h3, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h0, h12966, h12978, h9965, hc12, hc23, hlam, hphi, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h12966, hlam, p12982_0]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [h12967, hlam, p12982_1]
                        · have p12982_0 := h12982c.1
                          have p12982_1 := h12982c.2.1
                          have p12982_2 := h12982c.2.2.1
                          have p12982_3 := h12982c.2.2.2
                          linarith only [hlam, p12982_0]
                      · linarith only [h12967, h12981, h9965, hlam]
                    · linarith only [h0, h12966, h12977, h12980, h3, h7821, h9965, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h12978, h12979, h9965, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13137 | h13137
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13138 | h13138
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13139 | h13139
                      · rcases h0bigk with h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c | h13140c
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13142 | h13142
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13143 | h13143
                            · linarith only [h0, h13143, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13145 | h13145
                              · linarith only [h1, h13145, hlam]
                              · linarith only [h13145, h4, hlam]
                          · linarith only [h0, h13142, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13149 | h13149
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13150 | h13150
                            · linarith only [h0, h13150, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13152 | h13152
                              · linarith only [h1, h13152, hlam]
                              · rcases p13140_3 (m.d 0 4) (by simp) with h13154 | h13154
                                · linarith only [h13154, h2, hlam]
                                · linarith only [h13154, h9965, hlam]
                          · linarith only [h1, h13149, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13158 | h13158
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13159 | h13159
                            · linarith only [h0, h13159, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13161 | h13161
                              · linarith only [h1, h13161, hlam]
                              · rcases p13140_3 (m.d 0 4) (by simp) with h13163 | h13163
                                · linarith only [h13163, h2, hlam]
                                · rcases p13140_3 (m.d 0 5) (by simp) with h13165 | h13165
                                  · linarith only [h13165, h3, hlam]
                                  · rcases h2bigk with h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c | h13167c
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h13137, h9029, hc12, hc23, hlam, hphi, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h4, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h7821, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h9029, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h0, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12968, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12970, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12972, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12978, hc02, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12978, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12978, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h0, h12978, h9029, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      rcases p13167_3 (m.d 0 2) (by simp) with h13183 | h13183
                                      · linarith only [h13183, hlam, p13167_0]
                                      · rcases p13167_3 (m.d 1 2) (by simp) with h13185 | h13185
                                        · linarith only [h12970, h13185, hlam]
                                        · rcases p13167_3 (m.d 2 3) (by simp) with h13187 | h13187
                                          · linarith only [h12978, h13187, hlam]
                                          · linarith only [h13187, h4, hlam]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      rcases p13167_3 (m.d 0 2) (by simp) with h13190 | h13190
                                      · linarith only [h13190, h7821, hlam]
                                      · linarith only [h0, h13190, hlam]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h0, h12978, h4, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h0, h12978, h9029, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h0, h12978, h13137, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h12978, h13137, hc12, hc34, hlam, hphi, ht23, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h13137, hlam, p13167_1]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [h13138, hlam, p13167_0]
                                    · have p13167_0 := h13167c.1
                                      have p13167_1 := h13167c.2.1
                                      have p13167_2 := h13167c.2.2.1
                                      have p13167_3 := h13167c.2.2.2
                                      linarith only [hlam, p13167_0]
                          · linarith only [h13158, h2, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13202 | h13202
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13203 | h13203
                            · linarith only [h0, h13203, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13205 | h13205
                              · linarith only [h1, h13205, hlam]
                              · linarith only [h12966, h13205, hlam]
                          · linarith only [h13202, h3, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h0, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h4, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h7821, hlam, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h9029, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h1, hlam, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h0, h12978, h4, hc12, hc34, hlam, hphi, ht23, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h9965, hlam, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h0, h12978, h4, h9029, hc12, hc34, hlam, hphi, ht23, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h2, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13220 | h13220
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13221 | h13221
                            · linarith only [h13221, h7821, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13223 | h13223
                              · linarith only [h13223, h9965, hlam]
                              · linarith only [h13223, h4, hlam]
                          · linarith only [h0, h13220, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13227 | h13227
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13228 | h13228
                            · linarith only [h13228, h7821, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13230 | h13230
                              · linarith only [h13230, h9965, hlam]
                              · rcases p13140_3 (m.d 0 4) (by simp) with h13232 | h13232
                                · rcases p13140_3 (m.d 0 5) (by simp) with h13233 | h13233
                                  · linarith only [h12967, h13233, hlam]
                                  · rcases h2bigk with h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c | h13235c
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12978, h4, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h4, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h7821, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h9029, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h0, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12968, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12970, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12972, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12978, hc02, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12978, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12978, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h0, h12978, h9029, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      rcases p13235_3 (m.d 0 2) (by simp) with h13251 | h13251
                                      · linarith only [h13251, hlam, p13235_0]
                                      · rcases p13235_3 (m.d 1 2) (by simp) with h13253 | h13253
                                        · linarith only [h12970, h13253, hlam]
                                        · rcases p13235_3 (m.d 2 3) (by simp) with h13255 | h13255
                                          · linarith only [h12978, h13255, hlam]
                                          · linarith only [h13255, h4, hlam]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      rcases p13235_3 (m.d 0 2) (by simp) with h13258 | h13258
                                      · linarith only [h13258, h7821, hlam]
                                      · linarith only [h0, h13258, hlam]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h0, h12978, h4, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h0, h12978, h9029, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h0, h12978, h13137, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h12978, h13137, hc12, hc34, hlam, hphi, ht23, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h13137, hlam, p13235_1]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [h13138, hlam, p13235_0]
                                    · have p13235_0 := h13235c.1
                                      have p13235_1 := h13235c.2.1
                                      have p13235_2 := h13235c.2.2.1
                                      have p13235_3 := h13235c.2.2.2
                                      linarith only [hlam, p13235_0]
                                · linarith only [h13232, h9965, hlam]
                          · linarith only [h1, h13227, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          rcases p13140_3 (m.d 0 1) (by simp) with h13272 | h13272
                          · rcases p13140_3 (m.d 0 2) (by simp) with h13273 | h13273
                            · linarith only [h13273, h7821, hlam]
                            · rcases p13140_3 (m.d 0 3) (by simp) with h13275 | h13275
                              · linarith only [h13275, h9965, hlam]
                              · linarith only [h12966, h13275, hlam]
                          · linarith only [h13272, h3, hlam]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h3, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h0, h12978, h13137, h9029, hc12, hc34, hlam, hphi, ht23, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h12966, hlam, p13140_0]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [h12967, hlam, p13140_1]
                        · have p13140_0 := h13140c.1
                          have p13140_1 := h13140c.2.1
                          have p13140_2 := h13140c.2.2.1
                          have p13140_3 := h13140c.2.2.2
                          linarith only [hlam, p13140_0]
                      · linarith only [h0, h12978, h13139, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h12977, h13138, h2, h7821, hlam]
                  · linarith only [h0, h1, h12976, h13137, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h12974, h12976, h12977, hlam]
            · linarith only [h12966, h12976, h9965, hc13, hc34, hlam, hphi]
  · linarith only [h12966, h12967, h9965, hlam]

end R2N4
