import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11484000 in
set_option maxHeartbeats 11484000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h4961 | h4961
    · rcases m.htr 0 1 5 (by decide) (by decide) with h4962 | h4962
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4963 | h4963
        · linarith only [h0, h1, h4963, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4965 | h4965
          · rcases m.htr 0 2 5 (by decide) (by decide) with h4966 | h4966
            · rcases m.htr 0 3 4 (by decide) (by decide) with h4967 | h4967
              · rcases m.htr 0 3 5 (by decide) (by decide) with h4968 | h4968
                · rcases m.htr 0 4 5 (by decide) (by decide) with h4969 | h4969
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h4970 | h4970
                    · linarith only [h0, h1, h4963, h4965, h4970, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h4972 | h4972
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h4973 | h4973
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h4974 | h4974
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h4975 | h4975
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4976 | h4976
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4977 | h4977
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4978 | h4978
                                  · linarith only [h0, h1, h4970, h4972, h4978, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4980 | h4980
                                    · linarith only [h4976, h4978, h4980, hlam]
                                    · rcases h0bigk with h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4970, hc02, hc23, hlam, hphi, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4970, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4970, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h0, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4963, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h0, h1, h4961, h4970, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h0, h1, h4962, h4970, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4970, hc02, hc23, hlam, hphi, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4969, h4970, h4976, h4978, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h1, h4969, h4970, h4976, h4978, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4961, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4965, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4967, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h0, h4965, h4969, h4976, h4978, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4962, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4966, hlam, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4968, hlam, p4982_0]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [h4969, hlam, p4982_1]
                                      · have p4982_0 := h4982c.1
                                        have p4982_1 := h4982c.2.1
                                        have p4982_2 := h4982c.2.2.1
                                        have p4982_3 := h4982c.2.2.2
                                        linarith only [hlam, p4982_0]
                                · linarith only [h0, h1, h4970, h4972, h4976, h4977, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h1, h4970, h4972, h4976, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h4972, h4975, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h4972, h4974, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h4966, h4972, h4973, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h4965, h4970, h4972, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5014 | h5014
                    · linarith only [h0, h1, h4963, h5014, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5016 | h5016
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5017 | h5017
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5018 | h5018
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5019 | h5019
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5020 | h5020
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5021 | h5021
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5022 | h5022
                                  · linarith only [h0, h1, h5014, h5016, h5022, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5024 | h5024
                                    · linarith only [h1, h4961, h4969, h5014, h5016, h5020, h5024, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c | h5026c
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h0, h1, h5014, h5017, h5020, h5022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, h4961, h5014, h5016, h5020, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, h4961, h4969, h5014, h5016, h5020, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h0, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4963, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h0, h1, h4961, h5014, h5016, h5020, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h0, h1, h4961, h4969, h5014, h5016, h5020, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, h5014, hc01, hc23, hlam, hphi, ht12, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, h5014, hc02, hc23, hlam, hphi, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        rcases p5026_3 (m.d 0 1) (by simp) with h5040 | h5040
                                        · linarith only [h1, h5040, hlam]
                                        · linarith only [h4961, h5040, hlam]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        rcases p5026_3 (m.d 0 1) (by simp) with h5043 | h5043
                                        · linarith only [h1, h5043, hlam]
                                        · linarith only [h4962, h5043, hlam]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4961, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4965, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4967, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4969, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4962, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4966, hlam, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h4968, hlam, p5026_0]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [h1, h4961, h4962, h5014, h5016, h5020, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5026_1]
                                      · have p5026_0 := h5026c.1
                                        have p5026_1 := h5026c.2.1
                                        have p5026_2 := h5026c.2.2.1
                                        have p5026_3 := h5026c.2.2.2
                                        linarith only [hlam, p5026_0]
                                · linarith only [h0, h1, h5014, h5021, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h5014, h5020, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1, h5016, h5019, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5016, h5018, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h4966, h5016, h5017, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h4965, h5014, h5016, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h4966, h4968, hlam]
              · linarith only [h1, h4961, h4967, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5064 | h5064
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5065 | h5065
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5066 | h5066
                  · linarith only [h4965, h4966, h5066, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5068 | h5068
                    · linarith only [h0, h1, h4963, h5068, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5070 | h5070
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5071 | h5071
                        · linarith only [h0, h4966, h5071, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5073 | h5073
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5074 | h5074
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5075 | h5075
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5076 | h5076
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5077 | h5077
                                  · linarith only [h0, h1, h4961, h4966, h5066, h5068, h5070, h5077, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5079 | h5079
                                    · linarith only [h0, h4966, h5070, h5075, h5077, h5079, hlam]
                                    · rcases h0bigk with h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c | h5081c
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, h1, h5068, h5070, h5075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h1, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h1, h4961, h5068, h5070, h5075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, h1, h4966, h5068, h5070, h5075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4963, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4961, h4966, h5070, h5075, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4966, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, h5070, h5075, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h1, h5068, hc02, hc23, hlam, hphi, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        rcases p5081_3 (m.d 0 1) (by simp) with h5095 | h5095
                                        · linarith only [h1, h5095, hlam]
                                        · linarith only [h4961, h5095, hlam]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, h1, h4966, h5068, h5070, h5075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4961, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4965, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h5064, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h5066, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h4962, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h0, h5070, h5075, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h5065, hlam, p5081_0]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [h1, h4961, h4962, h5068, h5070, h5075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5081_1]
                                      · have p5081_0 := h5081c.1
                                        have p5081_1 := h5081c.2.1
                                        have p5081_2 := h5081c.2.2.1
                                        have p5081_3 := h5081c.2.2.2
                                        linarith only [hlam, p5081_0]
                                · linarith only [h0, h1, h5068, h5070, h5075, h5076, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1, h4962, h5068, h5070, h5071, h5075, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h4962, h5070, h5071, h5074, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h4962, h5070, h5071, h5073, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h4962, h4965, h4966, h5068, h5070, hc12, hc23, hlam, hphi]
                · linarith only [h1, h4962, h5065, hlam]
              · linarith only [h1, h4962, h4965, h4966, h5064, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5116 | h5116
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5117 | h5117
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5118 | h5118
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5119 | h5119
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5120 | h5120
                    · linarith only [h0, h1, h4963, h5120, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5122 | h5122
                      · linarith only [h0, h1, h4965, h5120, h5122, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5124 | h5124
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5125 | h5125
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5126 | h5126
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5127 | h5127
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5128 | h5128
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5129 | h5129
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5130 | h5130
                                    · rcases h0bigk with h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c | h5131c
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h0, h1, h5120, h5124, h5128, h5130, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h1, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h1, h5120, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h1, h5120, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h0, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h4963, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h4965, hlam, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h4962, h4965, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h0, h5124, h5128, h5130, hc03, hc45, hlam, hphi, ht0b, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h1, h5120, hc02, hc23, hlam, hphi, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h0, h1, h4965, h5120, h5124, h5128, h5130, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        rcases p5131_3 (m.d 0 1) (by simp) with h5146 | h5146
                                        · linarith only [h1, h5146, hlam]
                                        · linarith only [h4962, h5146, hlam]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h4961, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h0, h5124, h5128, h5130, hc04, hc45, hlam, hphi, ht0b, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h5117, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h1, h4961, h4962, h5120, h5124, h5128, h5130, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h4962, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h5116, hlam, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h5118, hlam, p5131_0]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [h5119, hlam, p5131_1]
                                      · have p5131_0 := h5131c.1
                                        have p5131_1 := h5131c.2.1
                                        have p5131_2 := h5131c.2.2.1
                                        have p5131_3 := h5131c.2.2.2
                                        linarith only [hlam, p5131_0]
                                    · linarith only [h1, h4961, h5120, h5122, h5124, h5129, h5130, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h4962, h4965, h5119, h5120, h5129, hc02, hc23, hlam, hphi]
                                · linarith only [h0, h1, h5120, h5124, h5128, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h4961, h5120, h5122, h5124, h5127, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h4961, h5122, h5124, h5126, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h4961, h5122, h5124, h5125, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h4961, h4965, h5116, h5120, h5124, hc12, hc23, hlam, hphi]
                  · linarith only [h4965, h5116, h5119, hlam]
                · linarith only [h1, h4961, h4965, h5116, h5118, hlam]
              · linarith only [h1, h4961, h5117, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5169 | h5169
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5170 | h5170
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5171 | h5171
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5172 | h5172
                    · linarith only [h0, h1, h4963, h5172, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5174 | h5174
                      · linarith only [h0, h4965, h5174, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5176 | h5176
                        · linarith only [h0, h5116, h5176, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5178 | h5178
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5179 | h5179
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5180 | h5180
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5181 | h5181
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5182 | h5182
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5183 | h5183
                                    · rcases h0bigk with h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c | h5184c
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h1, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h1, h5172, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h5116, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h4963, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h4965, hlam, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h5116, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h4961, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h1, h4961, h5172, h5178, h5183, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h5116, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h4961, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h4961, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h5169, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h4965, h5116, hc12, hc24, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h4962, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h0, h1, h4962, h5172, hc12, hc23, hlam, hphi, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h5170, hlam, p5184_0]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [h5171, hlam, p5184_1]
                                      · have p5184_0 := h5184c.1
                                        have p5184_1 := h5184c.2.1
                                        have p5184_2 := h5184c.2.2.1
                                        have p5184_3 := h5184c.2.2.2
                                        linarith only [hlam, p5184_0]
                                    · rcases h0bigk with h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c | h5210c
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h0, h1, h5172, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h5171, h5172, h5183, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h5172, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h0, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h4963, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h4965, hlam, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h5116, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h5172, hc01, hc23, hlam, hphi, ht12, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h0, h1, h5172, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h5171, h5172, h5183, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h4962, h5172, h5176, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h4961, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h0, h1, h4961, h5172, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h5169, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h1, h4961, h4962, h5172, h5176, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h4962, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h0, h1, h4962, h5172, hc12, hc23, hlam, hphi, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h5170, hlam, p5210_0]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [h5171, hlam, p5210_1]
                                      · have p5210_0 := h5210c.1
                                        have p5210_1 := h5210c.2.1
                                        have p5210_2 := h5210c.2.2.1
                                        have p5210_3 := h5210c.2.2.2
                                        linarith only [hlam, p5210_0]
                                  · linarith only [h4965, h5171, h5182, hlam]
                                · linarith only [h0, h1, h5172, h5181, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h4961, h5172, h5174, h5180, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h4961, h5174, h5179, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4961, h5174, h5178, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5241 | h5241
                    · linarith only [h0, h4963, h5241, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5243 | h5243
                      · linarith only [h0, h4965, h5243, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5245 | h5245
                        · linarith only [h0, h5116, h5245, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5247 | h5247
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5248 | h5248
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5249 | h5249
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5250 | h5250
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5251 | h5251
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5252 | h5252
                                    · linarith only [h1, h4961, h5171, h5247, h5252, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c | h5254c
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h1, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h4963, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h4965, hlam, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h5116, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h1, hc01, hc13, hlam, hphi, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h4963, hc12, hc23, hlam, hphi, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h4963, h4965, hc12, hc23, hlam, hphi, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h4963, h5116, hc12, hc23, hlam, hphi, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h4961, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h1, h4961, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h5169, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h5171, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h4962, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h0, h1, h4962, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h5170, hlam, p5254_0]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [h5171, h5249, h5251, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5254_1]
                                      · have p5254_0 := h5254c.1
                                        have p5254_1 := h5254c.2.1
                                        have p5254_2 := h5254c.2.2.1
                                        have p5254_3 := h5254c.2.2.2
                                        linarith only [hlam, p5254_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5280 | h5280
                                    · linarith only [h4965, h5251, h5280, hc02, hc34, hlam, hphi, ht23]
                                    · rcases h0bigk with h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h1, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h4965, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h1, h5241, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h4963, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h4965, hlam, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h5116, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h1, h5241, hc01, hc23, hlam, hphi, ht12, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h4965, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h1, h4962, h5241, h5245, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h4961, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h4961, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h5169, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h5171, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h4962, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h0, h1, h4962, h5241, hc12, hc23, hlam, hphi, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h5170, hlam, p5282_0]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [h1, h4962, h5241, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5282_1]
                                      · have p5282_0 := h5282c.1
                                        have p5282_1 := h5282c.2.1
                                        have p5282_2 := h5282c.2.2.1
                                        have p5282_3 := h5282c.2.2.2
                                        linarith only [hlam, p5282_0]
                                · linarith only [h0, h1, h5241, h5250, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h4961, h5241, h5243, h5249, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h4961, h5243, h5248, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4961, h5243, h5247, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h4962, h5170, hlam]
              · linarith only [h1, h4961, h5169, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5314 | h5314
        · linarith only [h0, h1, h5314, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5316 | h5316
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5317 | h5317
            · linarith only [h0, h4962, h5317, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5319 | h5319
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5320 | h5320
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5321 | h5321
                  · linarith only [h0, h4962, h5316, h5321, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5323 | h5323
                    · linarith only [h0, h1, h5314, h5323, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5325 | h5325
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5326 | h5326
                        · linarith only [h0, h4962, h5317, h5326, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5328 | h5328
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5329 | h5329
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5330 | h5330
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5331 | h5331
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5332 | h5332
                                  · linarith only [h0, h4962, h5321, h5325, h5332, hlam]
                                  · linarith only [h0, h4962, h5325, h5326, h5332, hc24, hc45, hlam, hphi]
                                · linarith only [h0, h4962, h5320, h5323, h5325, h5329, h5330, h5331, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h4962, h5323, h5325, h5329, h5330, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h5320, h5329, hlam]
                          · linarith only [h0, h1, h5325, h5328, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h5316, h5323, h5325, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5340 | h5340
                  · linarith only [h0, h1, h5316, h5320, h5340, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5342 | h5342
                    · linarith only [h0, h1, h5314, h5342, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5344 | h5344
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5345 | h5345
                        · linarith only [h0, h5317, h5345, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5347 | h5347
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5348 | h5348
                            · linarith only [h0, h1, h5320, h5342, h5344, h5348, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h5344, h5348, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5344, h5347, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5314, h5316, h5344, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h5316, h5319, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5354 | h5354
            · linarith only [h4961, h4962, h5316, h5354, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5356 | h5356
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5357 | h5357
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5358 | h5358
                  · linarith only [h4961, h4962, h5358, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5360 | h5360
                    · linarith only [h0, h5314, h5360, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5362 | h5362
                      · linarith only [h0, h5316, h5362, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5364 | h5364
                        · linarith only [h0, h4962, h5354, h5364, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5366 | h5366
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5367 | h5367
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5368 | h5368
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5369 | h5369
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5370 | h5370
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5371 | h5371
                                    · linarith only [h4961, h4962, h5316, h5358, h5366, h5367, h5371, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h0bigk with h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c | h5373c
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h4962, h5364, h5368, h5370, hc12, hc23, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h1, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h4962, h5364, h5368, h5370, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h4962, hlam, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5314, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5316, hlam, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5354, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h5314, hc12, hc23, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h5314, h5316, hc12, hc23, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h4962, h5314, hc12, hc23, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h4961, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h4961, h4962, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5356, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5358, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h4962, h5364, h5370, hc12, hc24, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h5357, hlam, p5373_0]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [h0, h4962, h5316, h5364, h5370, hc12, hc24, hlam, hphi, p5373_1]
                                      · have p5373_0 := h5373c.1
                                        have p5373_1 := h5373c.2.1
                                        have p5373_2 := h5373c.2.2.1
                                        have p5373_3 := h5373c.2.2.2
                                        linarith only [hlam, p5373_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5399 | h5399
                                    · linarith only [h1, h4961, h5360, h5366, h5370, h5399, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h4962, h5364, h5370, hc12, hc45, hlam, hphi, ht23, ht34, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h1, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h4962, h5364, h5370, hc04, hc45, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h4962, hlam, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5314, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5316, hlam, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5354, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h1, hc01, hc13, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h1, h5360, hc12, hc23, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h1, h5316, h5360, hc12, hc23, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h1, h4962, h5360, hc12, hc23, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h4961, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h1, h4961, h5360, hc12, hc23, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5356, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5358, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h0, h4962, h5364, h5370, hc12, hc45, hlam, hphi, ht23, ht34, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h5357, hlam, p5401_0]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [h4962, h5364, h5370, hc04, hc45, hlam, hphi, p5401_1]
                                      · have p5401_0 := h5401c.1
                                        have p5401_1 := h5401c.2.1
                                        have p5401_2 := h5401c.2.2.1
                                        have p5401_3 := h5401c.2.2.2
                                        linarith only [hlam, p5401_0]
                                · linarith only [h1, h5357, h5360, h5369, hlam]
                              · linarith only [h1, h4961, h5360, h5362, h5368, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5357, h5367, hlam]
                          · linarith only [h1, h4961, h5362, h5366, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5431 | h5431
                  · linarith only [h1, h4961, h5357, h5431, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5433 | h5433
                    · linarith only [h0, h1, h5357, h5433, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5435 | h5435
                      · linarith only [h0, h1, h5316, h5357, h5435, hc02, hc35, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5437 | h5437
                        · linarith only [h0, h5354, h5437, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5439 | h5439
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5440 | h5440
                            · linarith only [h0, h1, h5357, h5433, h5440, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h4961, h5435, h5440, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h4961, h5435, h5439, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h4961, h5356, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5445 | h5445
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5446 | h5446
        · linarith only [h0, h1, h5446, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5448 | h5448
          · linarith only [h0, h4961, h5448, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5450 | h5450
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5451 | h5451
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5452 | h5452
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5453 | h5453
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5454 | h5454
                    · linarith only [h0, h1, h5446, h5450, h5454, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5456 | h5456
                      · linarith only [h0, h4961, h5448, h5456, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5458 | h5458
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5459 | h5459
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5460 | h5460
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5461 | h5461
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5462 | h5462
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5463 | h5463
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5464 | h5464
                                    · rcases h0bigk with h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c | h5465c
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h4961, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h1, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h4961, hlam, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h4961, h5456, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5446, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5448, hlam, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, h4961, h5445, h5456, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h1, h5454, hc02, hc23, hlam, hphi, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, h1, h4961, h5454, h5458, h5462, h5464, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        rcases p5465_3 (m.d 0 1) (by simp) with h5480 | h5480
                                        · linarith only [h1, h5480, hlam]
                                        · linarith only [h5445, h5480, hlam]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, h5458, h5462, h5464, hc04, hc45, hlam, hphi, ht0b, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h0, h5458, h5462, h5464, hc04, hc45, hlam, hphi, ht0b, ht5b, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5451, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        rcases p5465_3 (m.d 0 1) (by simp) with h5487 | h5487
                                        · linarith only [h4961, h5487, hlam]
                                        · linarith only [h5445, h5487, hlam]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5445, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5450, hlam, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5452, hlam, p5465_0]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [h5453, hlam, p5465_1]
                                      · have p5465_0 := h5465c.1
                                        have p5465_1 := h5465c.2.1
                                        have p5465_2 := h5465c.2.2.1
                                        have p5465_3 := h5465c.2.2.2
                                        linarith only [hlam, p5465_0]
                                    · linarith only [h0, h1, h5454, h5458, h5463, h5464, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h5448, h5453, h5463, hlam]
                                · linarith only [h0, h4961, h5454, h5459, h5462, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h4961, h5454, h5458, h5459, h5461, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h4961, h5458, h5459, h5460, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h5451, h5459, hlam]
                        · linarith only [h0, h1, h5450, h5454, h5458, hc12, hc23, hlam, hphi]
                  · linarith only [h4961, h5445, h5453, hlam]
                · linarith only [h0, h1, h5450, h5452, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5504 | h5504
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5505 | h5505
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5506 | h5506
                    · linarith only [h0, h1, h5451, h5506, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5508 | h5508
                      · linarith only [h0, h1, h5448, h5451, h5508, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5510 | h5510
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5511 | h5511
                          · linarith only [h0, h1, h5451, h5506, h5510, h5511, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h5510, h5511, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h4961, h5450, h5508, h5510, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h5450, h5451, h5505, hlam]
                · linarith only [h0, h1, h5450, h5504, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5517 | h5517
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5518 | h5518
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5519 | h5519
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5520 | h5520
                    · linarith only [h0, h1, h5446, h5520, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5522 | h5522
                      · linarith only [h0, h5448, h5522, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5524 | h5524
                        · linarith only [h0, h5450, h5524, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5526 | h5526
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5527 | h5527
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5528 | h5528
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5529 | h5529
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5530 | h5530
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5531 | h5531
                                    · rcases h0bigk with h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c | h5532c
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h4961, h5520, h5526, hc02, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h1, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h4961, hlam, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h4961, h5450, h5520, h5526, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5446, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5448, hlam, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5450, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h1, h5520, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h1, h4961, h5445, h5520, h5524, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h1, h5450, h5520, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5445, h5524, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h4961, h5522, hc12, hc24, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5517, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h1, h5450, h5517, h5520, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5445, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h0, h1, h5445, h5520, hc12, hc23, hlam, hphi, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5518, hlam, p5532_0]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [h5519, hlam, p5532_1]
                                      · have p5532_0 := h5532c.1
                                        have p5532_1 := h5532c.2.1
                                        have p5532_2 := h5532c.2.2.1
                                        have p5532_3 := h5532c.2.2.2
                                        linarith only [hlam, p5532_0]
                                    · rcases h0bigk with h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c | h5558c
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h0, h4961, h5520, h5526, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h1, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h4961, hlam, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h4961, h5520, h5526, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h0, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5446, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5448, hlam, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5450, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h1, h5520, hc01, hc23, hlam, hphi, ht12, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h0, h1, h5520, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h1, h4961, h5445, h5520, h5524, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h1, h5445, h5520, h5524, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5445, h5524, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h0, h4961, h5520, h5526, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5517, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h4961, h5445, h5520, h5524, h5526, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5445, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h0, h1, h5445, h5520, hc12, hc23, hlam, hphi, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5518, hlam, p5558_0]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [h5519, hlam, p5558_1]
                                      · have p5558_0 := h5558c.1
                                        have p5558_1 := h5558c.2.1
                                        have p5558_2 := h5558c.2.2.1
                                        have p5558_3 := h5558c.2.2.2
                                        linarith only [hlam, p5558_0]
                                  · linarith only [h5448, h5519, h5530, hlam]
                                · linarith only [h0, h1, h5520, h5529, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h4961, h5445, h5520, h5524, h5526, h5528, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4961, h5445, h5524, h5526, h5527, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5445, h5517, h5524, h5526, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h4961, h5445, h5519, hlam]
                · linarith only [h1, h5445, h5518, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5591 | h5591
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5592 | h5592
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5593 | h5593
                    · linarith only [h0, h1, h5517, h5593, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5595 | h5595
                      · linarith only [h0, h5448, h5595, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5597 | h5597
                        · linarith only [h0, h5450, h5597, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5599 | h5599
                          · linarith only [h1, h5445, h5517, h5593, h5597, h5599, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h5445, h5597, h5599, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h5445, h5517, h5592, hlam]
                · linarith only [h1, h5445, h5591, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5604 | h5604
        · linarith only [h0, h1, h5604, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5606 | h5606
          · linarith only [h0, h4961, h5606, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5608 | h5608
            · linarith only [h0, h5445, h5608, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5610 | h5610
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5611 | h5611
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5612 | h5612
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5613 | h5613
                    · linarith only [h0, h1, h5604, h5613, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5615 | h5615
                      · linarith only [h0, h1, h5606, h5612, h5613, h5615, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5617 | h5617
                        · linarith only [h0, h5445, h5608, h5617, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5619 | h5619
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5620 | h5620
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5621 | h5621
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5622 | h5622
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5623 | h5623
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5624 | h5624
                                    · rcases h0bigk with h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5445, h5617, h5621, h5623, hc02, hc23, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h1, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h4961, hlam, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5445, hlam, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5604, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5606, hlam, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5608, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5604, hc12, hc23, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5445, h5604, h5612, hc12, hc23, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5445, h5604, hc12, hc23, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5606, hc12, hc24, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5610, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5445, h5604, h5610, hc12, hc23, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h0, h5445, h5617, hc12, hc25, hlam, hphi, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5611, hlam, p5625_0]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [h5612, hlam, p5625_1]
                                      · have p5625_0 := h5625c.1
                                        have p5625_1 := h5625c.2.1
                                        have p5625_2 := h5625c.2.2.1
                                        have p5625_3 := h5625c.2.2.2
                                        linarith only [hlam, p5625_0]
                                    · rcases h0bigk with h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c | h5651c
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h1, h5613, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h1, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h4961, hlam, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5445, hlam, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5604, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5606, hlam, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5608, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h1, h5613, hc01, hc23, hlam, hphi, ht12, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h1, h5613, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h1, h5612, h5613, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h1, h5445, h5613, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h4961, h5613, h5619, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5610, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h4961, h5445, h5613, h5619, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h0, h5445, h5617, h5621, h5623, hc12, hc23, hlam, hphi, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5611, hlam, p5651_0]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [h5612, hlam, p5651_1]
                                      · have p5651_0 := h5651c.1
                                        have p5651_1 := h5651c.2.1
                                        have p5651_2 := h5651c.2.2.1
                                        have p5651_3 := h5651c.2.2.2
                                        linarith only [hlam, p5651_0]
                                  · linarith only [h5606, h5612, h5623, hlam]
                                · linarith only [h0, h1, h5613, h5622, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h5613, h5621, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5611, h5620, hlam]
                          · linarith only [h1, h5610, h5619, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5682 | h5682
                    · linarith only [h0, h4961, h5612, h5682, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5684 | h5684
                      · linarith only [h0, h4961, h5612, h5684, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5686 | h5686
                        · linarith only [h0, h5608, h5686, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5688 | h5688
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5689 | h5689
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5690 | h5690
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5691 | h5691
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5692 | h5692
                                  · linarith only [h0, h4961, h5612, h5692, hc12, hc24, hlam, hphi]
                                  · linarith only [h0, h4961, h5684, h5692, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h5604, h5611, h5691, hlam]
                              · linarith only [h0, h1, h5682, h5690, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5611, h5689, hlam]
                          · linarith only [h1, h5610, h5688, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5699 | h5699
                  · linarith only [h5610, h5611, h5699, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5701 | h5701
                    · linarith only [h0, h1, h5611, h5701, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5703 | h5703
                      · linarith only [h0, h4961, h5699, h5703, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5705 | h5705
                        · linarith only [h0, h5608, h5705, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5707 | h5707
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5708 | h5708
                            · linarith only [h0, h1, h5611, h5701, h5708, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h5708, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h5610, h5707, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5712 | h5712
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5713 | h5713
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5714 | h5714
                    · linarith only [h0, h5604, h5714, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5716 | h5716
                      · linarith only [h0, h5606, h5716, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5718 | h5718
                        · linarith only [h0, h5445, h5608, h5718, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5720 | h5720
                          · linarith only [h0, h5445, h5610, h5712, h5714, h5720, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5720, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h5610, h5712, h5713, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5724 | h5724
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5725 | h5725
                    · linarith only [h0, h1, h5712, h5725, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5727 | h5727
                      · linarith only [h0, h5606, h5727, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5729 | h5729
                        · linarith only [h0, h5608, h5729, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5731 | h5731
                          · linarith only [h0, h1, h5610, h5725, h5731, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5731, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5734 | h5734
                    · linarith only [h0, h1, h5610, h5724, h5734, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5736 | h5736
                      · linarith only [h0, h1, h5606, h5610, h5736, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5738 | h5738
                        · linarith only [h0, h1, h5608, h5610, h5724, h5738, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5740 | h5740
                          · linarith only [h0, h1, h5610, h5734, h5740, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5740, hc12, hc34, hlam, hphi, ht23]

end R2N4
