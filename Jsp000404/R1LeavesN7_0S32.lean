import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18118 | h18118
  · rcases p17727_3 (m.d 1 2) (by simp) with h18119 | h18119
    · rcases p17727_3 (m.d 1 3) (by simp) with h18120 | h18120
      · linarith only [h16969, h18120, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h18122 | h18122
        · linarith only [h16970, h18122, hlam]
        · rcases p17727_3 (m.d 1 5) (by simp) with h18124 | h18124
          · linarith only [h16971, h18124, hlam]
          · rcases h1emax with h18126 | h18126 | h18126 | h18126 | h18126
            · linarith only [h0, h16970, h16976, h16978, h18126, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1]
            · linarith only [h16970, h16976, h16978, h18126, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1]
            · rcases h2bigk with h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c | h18129c
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16970, h16976, h16978, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18132 | h18132
                · rcases p18129_3 (m.d 1 2) (by simp) with h18133 | h18133
                  · linarith only [h0, h18133, hlam]
                  · linarith only [h16969, h18133, hlam]
                · linarith only [h18132, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18137 | h18137
                · rcases p18129_3 (m.d 1 2) (by simp) with h18138 | h18138
                  · linarith only [h0, h18138, hlam]
                  · linarith only [h16970, h18138, hlam]
                · linarith only [h18137, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18142 | h18142
                · rcases p18129_3 (m.d 1 2) (by simp) with h18143 | h18143
                  · linarith only [h0, h18143, hlam]
                  · linarith only [h16971, h18143, hlam]
                · linarith only [h18142, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h0, hlam, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18149 | h18149
                · rcases p18129_3 (m.d 1 2) (by simp) with h18150 | h18150
                  · rcases p18129_3 (m.d 2 3) (by simp) with h18151 | h18151
                    · linarith only [h18151, hlam, p18129_0]
                    · rcases p18129_3 (m.d 2 4) (by simp) with h18153 | h18153
                      · linarith only [h16970, h18153, hlam]
                      · linarith only [h16978, h18153, hlam]
                  · linarith only [h18150, hlam, p18129_0]
                · linarith only [h18149, h4, hlam]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18158 | h18158
                · rcases p18129_3 (m.d 1 2) (by simp) with h18159 | h18159
                  · rcases p18129_3 (m.d 2 3) (by simp) with h18160 | h18160
                    · linarith only [h16969, h18160, hlam]
                    · rcases p18129_3 (m.d 2 4) (by simp) with h18162 | h18162
                      · linarith only [h18162, hlam, p18129_0]
                      · rcases p18129_3 (m.d 2 5) (by simp) with h18164 | h18164
                        · linarith only [h16971, h18164, hlam]
                        · linarith only [h16982, h18164, hlam]
                  · linarith only [h18159, hlam, p18129_0]
                · linarith only [h18158, h5, hlam]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                rcases p18129_3 (m.d 0 2) (by simp) with h18169 | h18169
                · rcases p18129_3 (m.d 1 2) (by simp) with h18170 | h18170
                  · rcases p18129_3 (m.d 2 3) (by simp) with h18171 | h18171
                    · linarith only [h16969, h18171, hlam]
                    · rcases p18129_3 (m.d 2 4) (by simp) with h18173 | h18173
                      · linarith only [h16970, h18173, hlam]
                      · rcases p18129_3 (m.d 2 5) (by simp) with h18175 | h18175
                        · linarith only [h18175, hlam, p18129_0]
                        · rcases h4bigk with h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c | h18177c
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16970, h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h7, hlam, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h14159, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h2, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16976, h16978, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16972, hlam, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16976, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h5, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16970, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16978, hlam, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16982, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h16984, hlam, p18177_0]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            rcases p18177_3 (m.d 0 4) (by simp) with h18198 | h18198
                            · linarith only [h18198, hlam, p18177_0]
                            · rcases p18177_3 (m.d 1 4) (by simp) with h18200 | h18200
                              · linarith only [h16976, h18200, hlam]
                              · rcases p18177_3 (m.d 2 4) (by simp) with h18202 | h18202
                                · linarith only [h16982, h18202, hlam]
                                · rcases p18177_3 (m.d 3 4) (by simp) with h18204 | h18204
                                  · linarith only [h16984, h18204, hlam]
                                  · linarith only [h18204, h7, hlam]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            rcases p18177_3 (m.d 0 4) (by simp) with h18207 | h18207
                            · linarith only [h14159, h18207, hlam]
                            · linarith only [h18207, h2, hlam]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            rcases p18177_3 (m.d 0 4) (by simp) with h18210 | h18210
                            · linarith only [h14159, h18210, hlam]
                            · linarith only [h18210, h5, hlam]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18177_1]
                          · have p18177_0 := h18177c.1
                            have p18177_1 := h18177c.2.1
                            have p18177_2 := h18177c.2.2.1
                            have p18177_3 := h18177c.2.2.2
                            linarith only [hlam, p18177_0]
                  · linarith only [h18170, hlam, p18129_0]
                · linarith only [h18169, h6, hlam]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h4, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16969, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16978, hlam, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16980, hlam, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h5, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16970, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16982, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h6, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h16971, hlam, p18129_0]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18129_1]
              · have p18129_0 := h18129c.1
                have p18129_1 := h18129c.2.1
                have p18129_2 := h18129c.2.2.1
                have p18129_3 := h18129c.2.2.2
                linarith only [hlam, p18129_0]
            · rcases h2bigk with h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c | h18232c
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16976, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18235 | h18235
                · rcases p18232_3 (m.d 1 2) (by simp) with h18236 | h18236
                  · linarith only [h0, h18236, hlam]
                  · linarith only [h16969, h18236, hlam]
                · linarith only [h18235, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18240 | h18240
                · rcases p18232_3 (m.d 1 2) (by simp) with h18241 | h18241
                  · linarith only [h0, h18241, hlam]
                  · linarith only [h16970, h18241, hlam]
                · linarith only [h18240, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18245 | h18245
                · rcases p18232_3 (m.d 1 2) (by simp) with h18246 | h18246
                  · linarith only [h0, h18246, hlam]
                  · linarith only [h16971, h18246, hlam]
                · linarith only [h18245, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h0, hlam, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18252 | h18252
                · rcases p18232_3 (m.d 1 2) (by simp) with h18253 | h18253
                  · rcases p18232_3 (m.d 2 3) (by simp) with h18254 | h18254
                    · linarith only [h18254, hlam, p18232_0]
                    · rcases p18232_3 (m.d 2 4) (by simp) with h18256 | h18256
                      · linarith only [h16970, h18256, hlam]
                      · linarith only [h16978, h18256, hlam]
                  · linarith only [h18253, hlam, p18232_0]
                · linarith only [h18252, h4, hlam]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18261 | h18261
                · rcases p18232_3 (m.d 1 2) (by simp) with h18262 | h18262
                  · rcases p18232_3 (m.d 2 3) (by simp) with h18263 | h18263
                    · linarith only [h16969, h18263, hlam]
                    · rcases p18232_3 (m.d 2 4) (by simp) with h18265 | h18265
                      · linarith only [h18265, hlam, p18232_0]
                      · rcases p18232_3 (m.d 2 5) (by simp) with h18267 | h18267
                        · linarith only [h16971, h18267, hlam]
                        · linarith only [h16982, h18267, hlam]
                  · linarith only [h18262, hlam, p18232_0]
                · linarith only [h18261, h5, hlam]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                rcases p18232_3 (m.d 0 2) (by simp) with h18272 | h18272
                · rcases p18232_3 (m.d 1 2) (by simp) with h18273 | h18273
                  · rcases p18232_3 (m.d 2 3) (by simp) with h18274 | h18274
                    · linarith only [h16969, h18274, hlam]
                    · rcases p18232_3 (m.d 2 4) (by simp) with h18276 | h18276
                      · linarith only [h16970, h18276, hlam]
                      · rcases p18232_3 (m.d 2 5) (by simp) with h18278 | h18278
                        · linarith only [h18278, hlam, p18232_0]
                        · rcases h4bigk with h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c | h18280c
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16970, h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h7, hlam, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h14159, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h2, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16976, h16978, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16972, hlam, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16976, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h5, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16970, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16978, hlam, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16982, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h16984, hlam, p18280_0]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            rcases p18280_3 (m.d 0 4) (by simp) with h18301 | h18301
                            · linarith only [h18301, hlam, p18280_0]
                            · rcases p18280_3 (m.d 1 4) (by simp) with h18303 | h18303
                              · linarith only [h16976, h18303, hlam]
                              · rcases p18280_3 (m.d 2 4) (by simp) with h18305 | h18305
                                · linarith only [h16982, h18305, hlam]
                                · rcases p18280_3 (m.d 3 4) (by simp) with h18307 | h18307
                                  · linarith only [h16984, h18307, hlam]
                                  · linarith only [h18307, h7, hlam]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            rcases p18280_3 (m.d 0 4) (by simp) with h18310 | h18310
                            · linarith only [h14159, h18310, hlam]
                            · linarith only [h18310, h2, hlam]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            rcases p18280_3 (m.d 0 4) (by simp) with h18313 | h18313
                            · linarith only [h14159, h18313, hlam]
                            · linarith only [h18313, h5, hlam]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18280_1]
                          · have p18280_0 := h18280c.1
                            have p18280_1 := h18280c.2.1
                            have p18280_2 := h18280c.2.2.1
                            have p18280_3 := h18280c.2.2.2
                            linarith only [hlam, p18280_0]
                  · linarith only [h18273, hlam, p18232_0]
                · linarith only [h18272, h6, hlam]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h4, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16969, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16978, hlam, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16980, hlam, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h5, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16970, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16982, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h6, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h16971, hlam, p18232_0]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18232_1]
              · have p18232_0 := h18232c.1
                have p18232_1 := h18232c.2.1
                have p18232_2 := h18232c.2.2.1
                have p18232_3 := h18232c.2.2.2
                linarith only [hlam, p18232_0]
            · rcases h2bigk with h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c | h18335c
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16976, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18338 | h18338
                · rcases p18335_3 (m.d 1 2) (by simp) with h18339 | h18339
                  · linarith only [h0, h18339, hlam]
                  · linarith only [h16969, h18339, hlam]
                · linarith only [h18338, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18343 | h18343
                · rcases p18335_3 (m.d 1 2) (by simp) with h18344 | h18344
                  · linarith only [h0, h18344, hlam]
                  · linarith only [h16970, h18344, hlam]
                · linarith only [h18343, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18348 | h18348
                · rcases p18335_3 (m.d 1 2) (by simp) with h18349 | h18349
                  · linarith only [h0, h18349, hlam]
                  · linarith only [h16971, h18349, hlam]
                · linarith only [h18348, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h0, hlam, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18355 | h18355
                · rcases p18335_3 (m.d 1 2) (by simp) with h18356 | h18356
                  · rcases p18335_3 (m.d 2 3) (by simp) with h18357 | h18357
                    · linarith only [h18357, hlam, p18335_0]
                    · rcases p18335_3 (m.d 2 4) (by simp) with h18359 | h18359
                      · linarith only [h16970, h18359, hlam]
                      · linarith only [h16978, h18359, hlam]
                  · linarith only [h18356, hlam, p18335_0]
                · linarith only [h18355, h4, hlam]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18364 | h18364
                · rcases p18335_3 (m.d 1 2) (by simp) with h18365 | h18365
                  · rcases p18335_3 (m.d 2 3) (by simp) with h18366 | h18366
                    · linarith only [h16969, h18366, hlam]
                    · rcases p18335_3 (m.d 2 4) (by simp) with h18368 | h18368
                      · linarith only [h18368, hlam, p18335_0]
                      · rcases p18335_3 (m.d 2 5) (by simp) with h18370 | h18370
                        · linarith only [h16971, h18370, hlam]
                        · linarith only [h16982, h18370, hlam]
                  · linarith only [h18365, hlam, p18335_0]
                · linarith only [h18364, h5, hlam]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                rcases p18335_3 (m.d 0 2) (by simp) with h18375 | h18375
                · rcases p18335_3 (m.d 1 2) (by simp) with h18376 | h18376
                  · rcases p18335_3 (m.d 2 3) (by simp) with h18377 | h18377
                    · linarith only [h16969, h18377, hlam]
                    · rcases p18335_3 (m.d 2 4) (by simp) with h18379 | h18379
                      · linarith only [h16970, h18379, hlam]
                      · rcases p18335_3 (m.d 2 5) (by simp) with h18381 | h18381
                        · linarith only [h18381, hlam, p18335_0]
                        · rcases h4bigk with h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c | h18383c
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16970, h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16978, h16984, h7, hc23, hc45, hlam, hphi, ht34, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h7, hlam, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h14159, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h2, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16976, h16978, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17727_1, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16972, hlam, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16976, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h5, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16970, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16978, hlam, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16982, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16984, hc04, hc45, hlam, hphi, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16970, h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16978, h16984, hc23, hc45, hlam, hphi, ht34, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h16984, hlam, p18383_0]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            rcases p18383_3 (m.d 0 4) (by simp) with h18404 | h18404
                            · linarith only [h18404, hlam, p18383_0]
                            · rcases p18383_3 (m.d 1 4) (by simp) with h18406 | h18406
                              · linarith only [h16976, h18406, hlam]
                              · rcases p18383_3 (m.d 2 4) (by simp) with h18408 | h18408
                                · linarith only [h16982, h18408, hlam]
                                · rcases p18383_3 (m.d 3 4) (by simp) with h18410 | h18410
                                  · linarith only [h16984, h18410, hlam]
                                  · linarith only [h18410, h7, hlam]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            rcases p18383_3 (m.d 0 4) (by simp) with h18413 | h18413
                            · linarith only [h14159, h18413, hlam]
                            · linarith only [h18413, h2, hlam]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            rcases p18383_3 (m.d 0 4) (by simp) with h18416 | h18416
                            · linarith only [h14159, h18416, hlam]
                            · linarith only [h18416, h5, hlam]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [h1, h16969, h7, hc23, hc45, hlam, hphi, ht34, p18383_1]
                          · have p18383_0 := h18383c.1
                            have p18383_1 := h18383c.2.1
                            have p18383_2 := h18383c.2.2.1
                            have p18383_3 := h18383c.2.2.2
                            linarith only [hlam, p18383_0]
                  · linarith only [h18376, hlam, p18335_0]
                · linarith only [h18375, h6, hlam]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h4, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16969, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16978, hlam, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16980, hlam, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h5, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16970, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h14159, h16970, h2, hc23, hc45, hlam, hphi, ht34, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16982, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h6, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h16971, hlam, p18335_0]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h0, h16971, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17727_1, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [h0, h16971, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p17727_1, p18335_1]
              · have p18335_0 := h18335c.1
                have p18335_1 := h18335c.2.1
                have p18335_2 := h18335c.2.2.1
                have p18335_3 := h18335c.2.2.2
                linarith only [hlam, p18335_0]
    · linarith only [h16971, h18119, hlam]
  · linarith only [h18118, h3, hlam]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h1, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16969, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16972, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16974, hlam, p17727_1]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h2, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16970, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h14159, h16969, h2, hc23, hc45, hlam, hphi, ht34, p17727_1]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16976, hlam, p17727_1]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h3, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  linarith only [h16971, hlam, p17727_0]

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h16969 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h16970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h16971 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h16972 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h16974 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h16976 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h16978 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h16980 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h16982 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h16984 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h17727c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have p17727_0 := h17727c.1
  have p17727_1 := h17727c.2.1
  have p17727_2 := h17727c.2.2.1
  have p17727_3 := h17727c.2.2.2
  rcases p17727_3 (m.d 0 1) (by simp) with h18452 | h18452
  · rcases p17727_3 (m.d 1 2) (by simp) with h18453 | h18453
    · rcases p17727_3 (m.d 1 3) (by simp) with h18454 | h18454
      · linarith only [h16974, h18454, hlam]
      · rcases p17727_3 (m.d 1 4) (by simp) with h18456 | h18456
        · linarith only [h16976, h18456, hlam]
        · linarith only [h16972, h18456, hlam]
    · linarith only [h16969, h18453, hlam]
  · linarith only [h1, h18452, hlam]

end R2N4
