import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S14
import Jsp000404.R1LeavesN7_3S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h10368 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h10370 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 5 (by decide) (by decide) with h11081 | h11081
  · rcases m.htr 1 4 5 (by decide) (by decide) with h11082 | h11082
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11083 | h11083
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11084 | h11084
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11085 | h11085
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11086 | h11086
            · rcases h1bigk with h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c | h11087c
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                rcases p11087_3 (m.d 0 1) (by simp) with h11089 | h11089
                · rcases p11087_3 (m.d 1 2) (by simp) with h11090 | h11090
                  · linarith only [h11090, hlam, p11087_0]
                  · rcases p11087_3 (m.d 1 3) (by simp) with h11092 | h11092
                    · linarith only [h1, h11092, hlam]
                    · linarith only [h10364, h11092, hlam]
                · linarith only [h11089, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                rcases p11087_3 (m.d 0 1) (by simp) with h11096 | h11096
                · rcases p11087_3 (m.d 1 2) (by simp) with h11097 | h11097
                  · linarith only [h0, h11097, hlam]
                  · rcases p11087_3 (m.d 1 3) (by simp) with h11099 | h11099
                    · linarith only [h11099, hlam, p11087_0]
                    · rcases p11087_3 (m.d 1 4) (by simp) with h11101 | h11101
                      · linarith only [h11101, h2, hlam]
                      · linarith only [h10370, h11101, hlam]
                · linarith only [h11096, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                rcases p11087_3 (m.d 0 1) (by simp) with h11105 | h11105
                · rcases p11087_3 (m.d 1 2) (by simp) with h11106 | h11106
                  · linarith only [h0, h11106, hlam]
                  · rcases p11087_3 (m.d 1 3) (by simp) with h11108 | h11108
                    · linarith only [h1, h11108, hlam]
                    · rcases p11087_3 (m.d 1 4) (by simp) with h11110 | h11110
                      · linarith only [h11110, hlam, p11087_0]
                      · rcases p11087_3 (m.d 1 5) (by simp) with h11112 | h11112
                        · linarith only [h11112, h3, hlam]
                        · rcases h3bigk with h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c | h11114c
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            rcases p11114_3 (m.d 0 3) (by simp) with h11116 | h11116
                            · rcases p11114_3 (m.d 1 3) (by simp) with h11117 | h11117
                              · linarith only [h1, h11117, hlam]
                              · rcases p11114_3 (m.d 2 3) (by simp) with h11119 | h11119
                                · rcases p11114_3 (m.d 3 4) (by simp) with h11120 | h11120
                                  · linarith only [h10361, h11120, hlam]
                                  · linarith only [h10370, h11120, hlam]
                                · linarith only [h10364, h11119, hlam]
                            · linarith only [h1, h11116, hlam]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h4, hlam, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10370, h11081, h11086, hc03, hc45, hlam, hphi, ht0b, ht5b, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10361, h10370, h11081, hlam, p11114_2]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h1, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10364, hlam, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10370, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10370, h11086, hc01, hc45, hlam, hphi, ht0b, ht5b, p11087_1, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10361, h10368, h10370, h11081, hc12, hc23, hlam, hphi, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            rcases p11114_3 (m.d 0 3) (by simp) with h11134 | h11134
                            · linarith only [h11134, h4, hlam]
                            · linarith only [h1, h11134, hlam]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10370, h11081, h11086, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10361, h10370, h11081, h4, hlam, p11114_2]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10361, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10361, h11081, h11086, hc03, hc45, hlam, hphi, ht0b, ht5b, p11114_1]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h11083, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            rcases p11114_3 (m.d 0 3) (by simp) with h11144 | h11144
                            · rcases p11114_3 (m.d 1 3) (by simp) with h11145 | h11145
                              · linarith only [h10370, h11145, hlam]
                              · linarith only [h11081, h11145, hlam]
                            · linarith only [h10362, h11144, hlam]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h10362, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h11081, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h11084, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [h11086, hlam, p11114_0]
                          · have p11114_0 := h11114c.1
                            have p11114_1 := h11114c.2.1
                            have p11114_2 := h11114c.2.2.1
                            have p11114_3 := h11114c.2.2.2
                            linarith only [hlam, p11114_0]
                · linarith only [h11105, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                rcases p11087_3 (m.d 0 1) (by simp) with h11155 | h11155
                · rcases p11087_3 (m.d 1 2) (by simp) with h11156 | h11156
                  · linarith only [h0, h11156, hlam]
                  · rcases p11087_3 (m.d 1 3) (by simp) with h11158 | h11158
                    · linarith only [h1, h11158, hlam]
                    · linarith only [h11081, h11158, hlam]
                · linarith only [h11155, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h0, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10364, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10366, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10368, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h1, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10370, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10370, hlam, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10368, h10370, h4, hc12, hc23, hlam, hphi, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h2, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10370, h4, hc12, hc23, hlam, hphi, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10370, h11081, h4, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10368, h10370, h4, hc12, hc23, hlam, hphi, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h3, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h10361, h10370, h11081, h4, hc12, hc23, hlam, hphi, p11087_1]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h11081, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [h11082, hlam, p11087_0]
              · have p11087_0 := h11087c.1
                have p11087_1 := h11087c.2.1
                have p11087_2 := h11087c.2.2.1
                have p11087_3 := h11087c.2.2.2
                linarith only [hlam, p11087_0]
            · linarith only [h10363, h10364, h10370, h11083, h11086, h8674, hc12, hc23, hlam, hphi]
          · linarith only [h0, h10370, h11081, h11082, h11085, h8674, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h10361, h10370, h11084, h4, hc13, hc35, hlam, hphi]
      · linarith only [h10361, h11083, h4, hlam]
    · linarith only [h10370, h11081, h11082, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h11187 | h11187
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11188 | h11188
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11189 | h11189
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11190 | h11190
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11191 | h11191
            · rcases h1bigk with h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c | h11192c
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                rcases p11192_3 (m.d 0 1) (by simp) with h11194 | h11194
                · rcases p11192_3 (m.d 1 2) (by simp) with h11195 | h11195
                  · linarith only [h11195, hlam, p11192_0]
                  · rcases p11192_3 (m.d 1 3) (by simp) with h11197 | h11197
                    · linarith only [h1, h11197, hlam]
                    · linarith only [h10364, h11197, hlam]
                · linarith only [h11194, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                rcases p11192_3 (m.d 0 1) (by simp) with h11201 | h11201
                · rcases p11192_3 (m.d 1 2) (by simp) with h11202 | h11202
                  · linarith only [h0, h11202, hlam]
                  · rcases p11192_3 (m.d 1 3) (by simp) with h11204 | h11204
                    · linarith only [h11204, hlam, p11192_0]
                    · rcases p11192_3 (m.d 1 4) (by simp) with h11206 | h11206
                      · linarith only [h11206, h2, hlam]
                      · linarith only [h10370, h11206, hlam]
                · linarith only [h11201, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                rcases p11192_3 (m.d 0 1) (by simp) with h11210 | h11210
                · rcases p11192_3 (m.d 1 2) (by simp) with h11211 | h11211
                  · linarith only [h0, h11211, hlam]
                  · rcases p11192_3 (m.d 1 3) (by simp) with h11213 | h11213
                    · linarith only [h1, h11213, hlam]
                    · rcases p11192_3 (m.d 1 4) (by simp) with h11215 | h11215
                      · linarith only [h11215, hlam, p11192_0]
                      · rcases p11192_3 (m.d 1 5) (by simp) with h11217 | h11217
                        · linarith only [h11217, h3, hlam]
                        · rcases h3bigk with h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c | h11219c
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            rcases p11219_3 (m.d 0 3) (by simp) with h11221 | h11221
                            · rcases p11219_3 (m.d 1 3) (by simp) with h11222 | h11222
                              · linarith only [h1, h11222, hlam]
                              · rcases p11219_3 (m.d 2 3) (by simp) with h11224 | h11224
                                · rcases p11219_3 (m.d 3 4) (by simp) with h11225 | h11225
                                  · linarith only [h10361, h11225, hlam]
                                  · linarith only [h10370, h11225, hlam]
                                · linarith only [h10364, h11224, hlam]
                            · linarith only [h1, h11221, hlam]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h4, hlam, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10364, h10370, h4, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10364, h11081, h4, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h1, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10364, hlam, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10370, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h11081, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10361, h10364, h10370, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            rcases p11219_3 (m.d 0 3) (by simp) with h11239 | h11239
                            · linarith only [h11239, h4, hlam]
                            · linarith only [h1, h11239, hlam]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10364, h11081, h11191, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10364, h11081, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10361, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10361, h10364, h4, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h11188, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10361, h10364, h11081, h8674, hc12, hc24, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10362, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h10362, h10364, h4, hc12, hc23, hlam, hphi, p11219_1]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h11189, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [h11191, hlam, p11219_0]
                          · have p11219_0 := h11219c.1
                            have p11219_1 := h11219c.2.1
                            have p11219_2 := h11219c.2.2.1
                            have p11219_3 := h11219c.2.2.2
                            linarith only [hlam, p11219_0]
                · linarith only [h11210, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                rcases p11192_3 (m.d 0 1) (by simp) with h11256 | h11256
                · rcases p11192_3 (m.d 1 2) (by simp) with h11257 | h11257
                  · linarith only [h0, h11257, hlam]
                  · rcases p11192_3 (m.d 1 3) (by simp) with h11259 | h11259
                    · linarith only [h1, h11259, hlam]
                    · rcases p11192_3 (m.d 1 4) (by simp) with h11261 | h11261
                      · linarith only [h11261, h2, hlam]
                      · linarith only [h11187, h11261, hlam]
                · linarith only [h11256, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h0, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10364, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10366, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10368, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h1, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h10370, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10370, hlam, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h11081, hlam, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h2, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h10370, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h10364, h10370, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h10368, h10370, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h3, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h11081, h11191, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h10361, h10364, h11081, h11191, h4, hc12, hc23, hlam, hphi, p11192_1]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [h11187, hlam, p11192_0]
              · have p11192_0 := h11192c.1
                have p11192_1 := h11192c.2.1
                have p11192_2 := h11192c.2.2.1
                have p11192_3 := h11192c.2.2.2
                linarith only [hlam, p11192_0]
            · linarith only [h10370, h11187, h11191, hlam]
          · linarith only [h0, h10361, h10370, h11187, h11190, h4, h8674, hc12, hc23, hlam, hphi]
        · linarith only [h10362, h11189, h4, hlam]
      · linarith only [h10361, h11188, h4, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11289 | h11289
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11290 | h11290
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11291 | h11291
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11292 | h11292
            · linarith only [h10361, h10366, h11187, h11292, h4, hc12, hc23, hlam, hphi]
            · linarith only [h10361, h10363, h10364, h10370, h11292, h4, hc12, hc23, hlam, hphi]
          · linarith only [h10363, h11291, h8674, hlam]
        · linarith only [h10362, h11290, h4, hlam]
      · linarith only [h10361, h11289, h4, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h10368 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 4 (by decide) (by decide) with h10370 | h10370
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366 h10368 h10370
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366 h10368 h10370

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 5 (by decide) (by decide) with h10368 | h10368
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366 h10368
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366 h10368

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 4 (by decide) (by decide) with h10366 | h10366
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364 h10366

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 3 (by decide) (by decide) with h10364 | h10364
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h10364

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  linarith only [h0, h11298, h4, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  linarith only [h0, h11300, h8674, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  linarith only [h0, h11302, h9870, hlam]

end R2N4
