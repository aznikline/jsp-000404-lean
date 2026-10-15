import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S20
import Jsp000404.R1LeavesN7_9S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10776000 in
set_option maxHeartbeats 10776000 in
theorem r1l7_13_24_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h10295 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10296 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  rcases m.htr 0 2 4 (by decide) (by decide) with h11060 | h11060
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11061 | h11061
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11062 | h11062
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11063 | h11063
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11064 | h11064
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11065 | h11065
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11066 | h11066
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11067 | h11067
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11068 | h11068
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11069 | h11069
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11070 | h11070
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11071 | h11071
                        · linarith only [h10296, h11060, h11064, h11071, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h10296, h11060, h11063, h11064, h11071, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h10295, h10296, h11067, h11070, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h10295, h10296, h11060, h11061, h11067, h11069, h8811, hc03, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h10295, h11060, h11063, h11067, h11068, h8811, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h11062, h11067, h7360, hlam]
              · linarith only [h10296, h11060, h11061, h11064, h11066, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h10296, h11060, h11064, h11065, h8811, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11080 | h11080
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11081 | h11081
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11082 | h11082
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11083 | h11083
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11084 | h11084
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11085 | h11085
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11086 | h11086
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11087 | h11087
                          · rcases h3bigk with h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c | h11088c
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h7360, hlam, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h10296, hlam, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              rcases p11088_3 (m.d 0 3) (by simp) with h11092 | h11092
                              · rcases p11088_3 (m.d 1 3) (by simp) with h11093 | h11093
                                · rcases p11088_3 (m.d 2 3) (by simp) with h11094 | h11094
                                  · rcases p11088_3 (m.d 3 4) (by simp) with h11095 | h11095
                                    · linarith only [h11095, hlam, p11088_0]
                                    · rcases p11088_3 (m.d 3 5) (by simp) with h11097 | h11097
                                      · linarith only [h11062, h11097, hlam]
                                      · rcases h4bigk with h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c | h11099c
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h8811, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11084, h11087, hc04, hc45, hlam, hphi, ht0b, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11060, h11087, hc02, hc45, hlam, hphi, ht0b, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h11080, h8811, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h11080, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h11080, h11084, h11087, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h11080, h11087, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h11080, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11060, hlam, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11080, hlam, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11087, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11060, h11064, h11080, h8811, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11061, hlam, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11081, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11084, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11064, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11088_1, p11099_1]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11063, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11083, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11086, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [h11087, hlam, p11099_0]
                                        · have p11099_0 := h11099c.1
                                          have p11099_1 := h11099c.2.1
                                          have p11099_2 := h11099c.2.2.1
                                          have p11099_3 := h11099c.2.2.2
                                          linarith only [hlam, p11099_0]
                                  · linarith only [h11084, h11094, hlam]
                                · linarith only [h11081, h11093, hlam]
                              · linarith only [h11092, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              rcases p11088_3 (m.d 0 3) (by simp) with h11128 | h11128
                              · rcases p11088_3 (m.d 1 3) (by simp) with h11129 | h11129
                                · rcases p11088_3 (m.d 2 3) (by simp) with h11130 | h11130
                                  · rcases p11088_3 (m.d 3 4) (by simp) with h11131 | h11131
                                    · linarith only [h11061, h11131, hlam]
                                    · linarith only [h11087, h11131, hlam]
                                  · linarith only [h11085, h11130, hlam]
                                · linarith only [h11082, h11129, hlam]
                              · linarith only [h11128, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h10296, h11060, h11064, h11086, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11064, hlam, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              rcases p11088_3 (m.d 0 3) (by simp) with h11140 | h11140
                              · linarith only [h11140, h7360, hlam]
                              · linarith only [h11061, h11140, hlam]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              rcases p11088_3 (m.d 0 3) (by simp) with h11143 | h11143
                              · linarith only [h11143, h7360, hlam]
                              · linarith only [h11062, h11143, hlam]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h10296, h11060, h11084, h11087, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h10295, h11082, h11087, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              rcases p11088_3 (m.d 0 3) (by simp) with h11149 | h11149
                              · linarith only [h10296, h11149, hlam]
                              · linarith only [h11061, h11149, hlam]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h0, h10295, h11064, h11082, hlam, p11088_2]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11061, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11081, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11084, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h0, h11060, h11064, h11084, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11088_1]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11062, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11082, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11085, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [h11087, hlam, p11088_0]
                            · have p11088_0 := h11088c.1
                              have p11088_1 := h11088c.2.1
                              have p11088_2 := h11088c.2.2.1
                              have p11088_3 := h11088c.2.2.2
                              linarith only [hlam, p11088_0]
                          · linarith only [h10295, h11064, h11080, h11083, h11087, h8811, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h10295, h11064, h11080, h11083, h11086, h8811, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h11064, h11080, h11085, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h10295, h11064, h11080, h11083, h11084, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h10295, h11060, h11063, h11082, h11083, h8811, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h10295, h11062, h11064, h11080, h11082, h8811, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h10295, h10296, h11060, h11061, h11081, h7360, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h0, h11060, h11080, hlam]
        · linarith only [h10295, h11063, h8811, hlam]
      · linarith only [h0, h10295, h10296, h11062, hlam]
    · linarith only [h10296, h11060, h11061, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11174 | h11174
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11175 | h11175
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11176 | h11176
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11177 | h11177
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11178 | h11178
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11179 | h11179
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11180 | h11180
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11181 | h11181
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11182 | h11182
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11183 | h11183
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11184 | h11184
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11185 | h11185
                          · rcases h3bigk with h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c | h11186c
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h7360, hlam, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h10296, hlam, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h10296, h11177, h11185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              rcases p11186_3 (m.d 0 3) (by simp) with h11191 | h11191
                              · rcases p11186_3 (m.d 1 3) (by simp) with h11192 | h11192
                                · rcases p11186_3 (m.d 2 3) (by simp) with h11193 | h11193
                                  · rcases p11186_3 (m.d 3 4) (by simp) with h11194 | h11194
                                    · linarith only [h11174, h11194, hlam]
                                    · linarith only [h11185, h11194, hlam]
                                  · linarith only [h11183, h11193, hlam]
                                · linarith only [h11180, h11192, hlam]
                              · linarith only [h11191, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11174, h11185, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h0, h11060, h11177, h11182, hc01, hc12, hlam, hphi, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              rcases p11186_3 (m.d 0 3) (by simp) with h11203 | h11203
                              · linarith only [h11203, h7360, hlam]
                              · linarith only [h11174, h11203, hlam]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              rcases p11186_3 (m.d 0 3) (by simp) with h11206 | h11206
                              · linarith only [h11206, h7360, hlam]
                              · linarith only [h11175, h11206, hlam]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11174, h11185, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11177, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11177, h11185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              rcases p11186_3 (m.d 0 3) (by simp) with h11213 | h11213
                              · linarith only [h10296, h11213, hlam]
                              · linarith only [h11175, h11213, hlam]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11174, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11179, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11182, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h10296, h11174, h11177, h11185, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11186_1]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11175, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11180, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11183, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [h11185, hlam, p11186_0]
                            · have p11186_0 := h11186c.1
                              have p11186_1 := h11186c.2.1
                              have p11186_2 := h11186c.2.2.1
                              have p11186_3 := h11186c.2.2.2
                              linarith only [hlam, p11186_0]
                          · linarith only [h0, h10295, h10296, h11177, h11181, h11185, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h10295, h11060, h11181, h11184, hlam]
                      · linarith only [h0, h10295, h11060, h11180, h11182, h11183, hlam]
                    · linarith only [h10296, h11174, h11182, hlam]
                  · linarith only [h0, h10295, h11060, h11174, h11176, h11178, h11181, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h10296, h11175, h11177, h11180, hlam]
              · linarith only [h10296, h11174, h11177, h11179, hlam]
            · linarith only [h0, h10295, h10296, h11177, h11178, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11234 | h11234
            · linarith only [h0, h10295, h11060, h11177, h11234, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11236 | h11236
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11237 | h11237
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11238 | h11238
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11239 | h11239
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11240 | h11240
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11241 | h11241
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11242 | h11242
                          · rcases h3bigk with h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c | h11243c
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h7360, hlam, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h10296, hlam, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11247 | h11247
                              · rcases p11243_3 (m.d 1 3) (by simp) with h11248 | h11248
                                · rcases p11243_3 (m.d 2 3) (by simp) with h11249 | h11249
                                  · rcases p11243_3 (m.d 3 4) (by simp) with h11250 | h11250
                                    · linarith only [h11250, hlam, p11243_0]
                                    · rcases p11243_3 (m.d 3 5) (by simp) with h11252 | h11252
                                      · linarith only [h11175, h11252, hlam]
                                      · rcases h4bigk with h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c | h11254c
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h8811, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11060, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11242, hc04, hc45, hlam, hphi, ht0b, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          rcases p11254_3 (m.d 0 4) (by simp) with h11259 | h11259
                                          · rcases p11254_3 (m.d 1 4) (by simp) with h11260 | h11260
                                            · rcases p11254_3 (m.d 2 4) (by simp) with h11261 | h11261
                                              · rcases p11254_3 (m.d 3 4) (by simp) with h11262 | h11262
                                                · linarith only [h11174, h11262, hlam]
                                                · linarith only [h11242, h11262, hlam]
                                              · linarith only [h11241, h11261, hlam]
                                            · linarith only [h11238, h11260, hlam]
                                          · linarith only [h11259, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h10295, h11237, h11242, h8811, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11234, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11234, h11239, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          rcases p11254_3 (m.d 0 4) (by simp) with h11272 | h11272
                                          · linarith only [h11272, h8811, hlam]
                                          · linarith only [h11176, h11272, hlam]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h0, h10295, h11060, h11237, h11239, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h10295, h11237, h11239, h11242, h8811, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11239, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          rcases p11254_3 (m.d 0 4) (by simp) with h11279 | h11279
                                          · linarith only [h11060, h11279, hlam]
                                          · linarith only [h11176, h11279, hlam]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11174, hlam, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11236, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11239, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p11243_1, p11254_1]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11176, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11238, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11241, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [h11242, hlam, p11254_0]
                                        · have p11254_0 := h11254c.1
                                          have p11254_1 := h11254c.2.1
                                          have p11254_2 := h11254c.2.2.1
                                          have p11254_3 := h11254c.2.2.2
                                          linarith only [hlam, p11254_0]
                                  · linarith only [h11239, h11249, hlam]
                                · linarith only [h11236, h11248, hlam]
                              · linarith only [h11247, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11295 | h11295
                              · rcases p11243_3 (m.d 1 3) (by simp) with h11296 | h11296
                                · rcases p11243_3 (m.d 2 3) (by simp) with h11297 | h11297
                                  · rcases p11243_3 (m.d 3 4) (by simp) with h11298 | h11298
                                    · linarith only [h11174, h11298, hlam]
                                    · linarith only [h11242, h11298, hlam]
                                  · linarith only [h11240, h11297, hlam]
                                · linarith only [h11237, h11296, hlam]
                              · linarith only [h11295, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11174, h11177, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11177, hlam, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11307 | h11307
                              · linarith only [h11307, h7360, hlam]
                              · linarith only [h11174, h11307, hlam]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11310 | h11310
                              · linarith only [h11310, h7360, hlam]
                              · linarith only [h11175, h11310, hlam]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11174, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h10295, h11237, h11242, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11243_1]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11316 | h11316
                              · linarith only [h10296, h11316, hlam]
                              · linarith only [h11174, h11316, hlam]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h0, h10295, h11177, h11237, hlam, p11243_2]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11174, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11236, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11239, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              rcases p11243_3 (m.d 0 3) (by simp) with h11324 | h11324
                              · rcases p11243_3 (m.d 1 3) (by simp) with h11325 | h11325
                                · rcases p11243_3 (m.d 2 3) (by simp) with h11326 | h11326
                                  · rcases p11243_3 (m.d 3 4) (by simp) with h11327 | h11327
                                    · rcases p11243_3 (m.d 3 5) (by simp) with h11328 | h11328
                                      · linarith only [h11242, h11328, hlam]
                                      · rcases h4bigk with h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c | h11330c
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h8811, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11060, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11242, hc04, hc45, hlam, hphi, ht0b, ht5b, p11243_1, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          rcases p11330_3 (m.d 0 4) (by simp) with h11335 | h11335
                                          · rcases p11330_3 (m.d 1 4) (by simp) with h11336 | h11336
                                            · rcases p11330_3 (m.d 2 4) (by simp) with h11337 | h11337
                                              · rcases p11330_3 (m.d 3 4) (by simp) with h11338 | h11338
                                                · linarith only [h11174, h11338, hlam]
                                                · linarith only [h11242, h11338, hlam]
                                              · linarith only [h11241, h11337, hlam]
                                            · linarith only [h11238, h11336, hlam]
                                          · linarith only [h11335, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h10295, h11237, h11242, h8811, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11234, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11242, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11243_1, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          rcases p11330_3 (m.d 0 4) (by simp) with h11348 | h11348
                                          · linarith only [h11348, h8811, hlam]
                                          · linarith only [h11176, h11348, hlam]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11174, h11239, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11243_1, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h10295, h11237, h11239, h11242, h8811, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11239, h11242, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11243_1, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          rcases p11330_3 (m.d 0 4) (by simp) with h11355 | h11355
                                          · linarith only [h11060, h11355, hlam]
                                          · linarith only [h11176, h11355, hlam]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11174, hlam, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11236, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11239, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11174, hc03, hc45, hlam, hphi, ht0b, ht5b, p11330_1]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11176, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11238, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11241, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [h11242, hlam, p11330_0]
                                        · have p11330_0 := h11330c.1
                                          have p11330_1 := h11330c.2.1
                                          have p11330_2 := h11330c.2.2.1
                                          have p11330_3 := h11330c.2.2.2
                                          linarith only [hlam, p11330_0]
                                    · linarith only [h11242, h11327, hlam]
                                  · linarith only [h11240, h11326, hlam]
                                · linarith only [h11237, h11325, hlam]
                              · linarith only [h11175, h11324, hlam]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11175, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11237, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11240, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [h11242, hlam, p11243_0]
                            · have p11243_0 := h11243c.1
                              have p11243_1 := h11243c.2.1
                              have p11243_2 := h11243c.2.2.1
                              have p11243_3 := h11243c.2.2.2
                              linarith only [hlam, p11243_0]
                          · linarith only [h0, h10295, h11177, h11238, h11242, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h10295, h11234, h11238, h11241, hlam]
                      · linarith only [h0, h11234, h11239, h11240, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h11174, h11177, h11239, h7360, hlam]
                  · linarith only [h11174, h11176, h11238, h7360, h8811, hc01, hc13, hlam, hphi]
                · linarith only [h11175, h11237, h7360, hlam]
              · linarith only [h11174, h11236, h7360, hlam]
        · linarith only [h10295, h11176, h8811, hlam]
      · linarith only [h0, h10295, h11060, h11174, h11175, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11386 | h11386
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11387 | h11387
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11388 | h11388
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11389 | h11389
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11390 | h11390
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11391 | h11391
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11392 | h11392
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11393 | h11393
                    · linarith only [h0, h10295, h10296, h11174, h11388, h11391, h11393, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h10295, h10296, h11390, h11391, h11393, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h10295, h11387, h11391, h11392, h8811, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10296, h11174, h11390, h11391, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11398 | h11398
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11399 | h11399
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11400 | h11400
                    · linarith only [h11388, h11390, h11400, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11402 | h11402
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11403 | h11403
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11404 | h11404
                          · rcases h3bigk with h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c | h11405c
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h7360, hlam, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h10296, hlam, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11174, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              rcases p11405_3 (m.d 0 3) (by simp) with h11410 | h11410
                              · rcases p11405_3 (m.d 1 3) (by simp) with h11411 | h11411
                                · rcases p11405_3 (m.d 2 3) (by simp) with h11412 | h11412
                                  · rcases p11405_3 (m.d 3 4) (by simp) with h11413 | h11413
                                    · rcases p11405_3 (m.d 3 5) (by simp) with h11414 | h11414
                                      · linarith only [h11414, hlam, p11405_0]
                                      · rcases h4bigk with h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c | h11416c
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h8811, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11060, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11174, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11060, h11389, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h10295, h11398, h11404, h8811, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h0, h10295, h11060, h11389, h11398, h11404, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11390, hlam, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          rcases p11416_3 (m.d 0 4) (by simp) with h11426 | h11426
                                          · linarith only [h11426, h8811, hlam]
                                          · linarith only [h11387, h11426, hlam]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11174, h11404, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11405_1, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11389, hlam, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11400, hlam, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11389, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11174, h11404, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11405_1, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h10295, h11398, h11404, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h0, h10295, h11060, h11398, h11404, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11416_1]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          rcases p11416_3 (m.d 0 4) (by simp) with h11438 | h11438
                                          · linarith only [h11174, h11438, hlam]
                                          · linarith only [h11387, h11438, hlam]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11387, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11399, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11403, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [h11404, hlam, p11416_0]
                                        · have p11416_0 := h11416c.1
                                          have p11416_1 := h11416c.2.1
                                          have p11416_2 := h11416c.2.2.1
                                          have p11416_3 := h11416c.2.2.2
                                          linarith only [hlam, p11416_0]
                                    · linarith only [h11404, h11413, hlam]
                                  · linarith only [h11402, h11412, hlam]
                                · linarith only [h11398, h11411, hlam]
                              · linarith only [h11410, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11390, hc03, hc34, hlam, hphi, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h0, h10295, h10296, h11390, h11398, h11404, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11390, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              rcases p11405_3 (m.d 0 3) (by simp) with h11454 | h11454
                              · linarith only [h11454, h7360, hlam]
                              · linarith only [h11386, h11454, hlam]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h0, h10295, h10296, h11388, h11398, h11404, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11388, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11400, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              rcases p11405_3 (m.d 0 3) (by simp) with h11461 | h11461
                              · linarith only [h10296, h11461, hlam]
                              · linarith only [h11386, h11461, hlam]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              rcases p11405_3 (m.d 0 3) (by simp) with h11464 | h11464
                              · linarith only [h11464, hlam, p11405_0]
                              · rcases p11405_3 (m.d 1 3) (by simp) with h11466 | h11466
                                · linarith only [h11390, h11466, hlam]
                                · linarith only [h11466, h7360, hlam]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h10295, h11398, h11404, h7360, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h0, h10295, h10296, h11398, h11404, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11405_1]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h0, h10295, h10296, h11388, h11390, h11398, hlam, p11405_2]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11386, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11398, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11402, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [h11404, hlam, p11405_0]
                            · have p11405_0 := h11405c.1
                              have p11405_1 := h11405c.2.1
                              have p11405_2 := h11405c.2.2.1
                              have p11405_3 := h11405c.2.2.2
                              linarith only [hlam, p11405_0]
                          · linarith only [h0, h10295, h10296, h11388, h11390, h11398, h11404, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h10295, h10296, h11399, h11400, h11403, hlam]
                      · linarith only [h0, h10295, h10296, h11398, h11402, hlam]
                  · linarith only [h10295, h11387, h11398, h11399, h8811, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h10296, h11386, h11388, h11398, hlam]
            · linarith only [h0, h10295, h10296, h11388, h11389, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h11484 | h11484
            · linarith only [h0, h10295, h11060, h11388, h11484, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11486 | h11486
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11487 | h11487
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11488 | h11488
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11489 | h11489
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11490 | h11490
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11491 | h11491
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11492 | h11492
                          · rcases h3bigk with h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h7360, hlam, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h10296, hlam, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11174, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11174, h11388, h11486, h11492, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              rcases p11493_3 (m.d 0 3) (by simp) with h11499 | h11499
                              · linarith only [h11499, h7360, hlam]
                              · rcases p11493_3 (m.d 1 3) (by simp) with h11501 | h11501
                                · rcases p11493_3 (m.d 2 3) (by simp) with h11502 | h11502
                                  · rcases p11493_3 (m.d 3 4) (by simp) with h11503 | h11503
                                    · linarith only [h11486, h11503, hlam]
                                    · linarith only [h11174, h11503, hlam]
                                  · linarith only [h10296, h11502, hlam]
                                · linarith only [h11501, h7360, hlam]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11388, hlam, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h10295, h11174, h11388, h11487, h11492, h7360, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h0, h10295, h10296, h11174, h11486, h11487, hlam, p11493_2]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              rcases p11493_3 (m.d 0 3) (by simp) with h11512 | h11512
                              · linarith only [h10296, h11512, hlam]
                              · rcases p11493_3 (m.d 1 3) (by simp) with h11514 | h11514
                                · linarith only [h11388, h11514, hlam]
                                · linarith only [h11514, h7360, hlam]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h0, h10295, h10296, h11174, h11486, h11487, h11492, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h0, h10295, h10296, h11174, h11487, h11492, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h0, h10295, h11484, h11487, h11489, hlam, p11493_2]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h0, h10295, h10296, h11486, h11487, h11492, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p11493_1]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11486, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11489, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              rcases p11493_3 (m.d 0 3) (by simp) with h11525 | h11525
                              · linarith only [h11174, h11525, hlam]
                              · linarith only [h11386, h11525, hlam]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11386, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11487, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11490, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [h11492, hlam, p11493_0]
                            · have p11493_0 := h11493c.1
                              have p11493_1 := h11493c.2.1
                              have p11493_2 := h11493c.2.2.1
                              have p11493_3 := h11493c.2.2.2
                              linarith only [hlam, p11493_0]
                          · linarith only [h0, h10295, h10296, h11174, h11387, h11492, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h10295, h10296, h11174, h11484, h11488, h11491, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h10295, h10296, h11174, h11388, h11486, h11487, h11490, hlam]
                    · linarith only [h11388, h11486, h11489, hlam]
                  · linarith only [h11387, h11488, h8811, hlam]
                · linarith only [h0, h10295, h10296, h11174, h11486, h11487, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11539 | h11539
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11540 | h11540
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11541 | h11541
                    · linarith only [h0, h10295, h11388, h11486, h11539, h11541, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h10295, h11388, h11539, h11541, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h11387, h11540, h8811, hlam]
                · linarith only [h0, h10295, h11386, h11388, h11539, hc03, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h10295, h11174, h11387, h7360, hlam]
      · linarith only [h0, h10295, h10296, h11386, hlam]

set_option maxHeartbeats 10776000 in
set_option maxHeartbeats 10776000 in
theorem r1l7_13_24_L_I_H_I_s10_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h10295 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  rcases m.htr 0 2 3 (by decide) (by decide) with h10296 | h10296
  · exact r1l7_13_24_L_I_H_I_s10_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 h10295 h10296
  · exact r1l7_13_24_L_I_H_I_s10_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 h10295 h10296

set_option maxHeartbeats 10776000 in
set_option maxHeartbeats 10776000 in
theorem r1l7_13_24_L_I_H_I_s10_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  exact r1l7_13_24_L_I_H_I_s11 m hb3 hb4 h0 h7360 h8811 h10295

set_option maxHeartbeats 10776000 in
set_option maxHeartbeats 10776000 in
theorem r1l7_13_24_L_I_H_I_s10 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  rcases m.htr 0 1 5 (by decide) (by decide) with h10295 | h10295
  · exact r1l7_13_24_L_I_H_I_s10_x0 m hb3 hb4 hg0 hg7360 hg8811 h10295
  · exact r1l7_13_24_L_I_H_I_s10_x1 m hb3 hb4 hg0 hg7360 hg8811 h10295

end R2N4
