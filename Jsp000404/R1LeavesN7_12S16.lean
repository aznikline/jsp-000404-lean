import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8512000 in
set_option maxHeartbeats 8512000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7647 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  have h7647 := hg7647
  rcases m.htr 0 1 5 (by decide) (by decide) with h8170 | h8170
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8171 | h8171
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8172 | h8172
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8173 | h8173
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8174 | h8174
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8175 | h8175
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8176 | h8176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8177 | h8177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8178 | h8178
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8179 | h8179
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h8180 | h8180
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h8181 | h8181
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h8182 | h8182
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h8183 | h8183
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h8184 | h8184
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h8185 | h8185
                                · linarith only [h8171, h8182, h8185, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h1bigk with h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c | h8187c
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h0, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h6794, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h7647, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h7647, h8176, h8179, hc12, hlam, hphi, ht01, ht0b, ht5b, p8187_1, u5ehi1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8170, h8178, h8184, h8185, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h6794, hc01, hc12, hlam, hphi, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h7647, h8170, h8178, h8184, h8185, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    rcases p8187_3 (m.d 0 1) (by simp) with h8197 | h8197
                                    · linarith only [h0, h8197, hlam]
                                    · linarith only [h8170, h8197, hlam]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8170, h8178, h8184, h8185, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8176, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h7647, h8170, h8176, h8178, h8184, h8185, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    rcases p8187_3 (m.d 0 1) (by simp) with h8204 | h8204
                                    · linarith only [h6794, h8204, hlam]
                                    · linarith only [h8170, h8204, hlam]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8170, h8178, h8184, h8185, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8177, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8179, hlam, p8187_1]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    rcases p8187_3 (m.d 0 1) (by simp) with h8211 | h8211
                                    · linarith only [h7647, h8211, hlam]
                                    · linarith only [h8170, h8211, hlam]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8170, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8178, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8180, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [h8181, hlam, p8187_0]
                                  · have p8187_0 := h8187c.1
                                    have p8187_1 := h8187c.2.1
                                    have p8187_2 := h8187c.2.2.1
                                    have p8187_3 := h8187c.2.2.2
                                    linarith only [hlam, p8187_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h8219 | h8219
                                · linarith only [h0, h8171, h8182, h8184, h8219, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h1bigk with h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h0, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h6794, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h7647, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h7647, h8176, h8179, hc12, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi1]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8170, h8181, h8183, h8184, hc12, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi3]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h6794, hc01, hc12, hlam, hphi, p8221_1]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h7647, h8170, h8181, h8183, h8184, hc12, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi3]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    rcases p8221_3 (m.d 0 1) (by simp) with h8231 | h8231
                                    · linarith only [h0, h8231, hlam]
                                    · linarith only [h8170, h8231, hlam]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8170, h8181, h8183, h8184, hc13, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi3]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8176, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h7647, h8170, h8176, h8181, h8183, h8184, hc12, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi3]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    rcases p8221_3 (m.d 0 1) (by simp) with h8238 | h8238
                                    · linarith only [h6794, h8238, hlam]
                                    · linarith only [h8170, h8238, hlam]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8170, h8181, h8183, h8184, hc14, hlam, hphi, ht01, ht0b, ht5b, p8221_1, u5ehi3]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8177, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8179, hlam, p8221_1]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    rcases p8221_3 (m.d 0 1) (by simp) with h8245 | h8245
                                    · linarith only [h7647, h8245, hlam]
                                    · linarith only [h8170, h8245, hlam]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8170, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8178, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8180, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [h8181, hlam, p8221_0]
                                  · have p8221_0 := h8221c.1
                                    have p8221_1 := h8221c.2.1
                                    have p8221_2 := h8221c.2.2.1
                                    have p8221_3 := h8221c.2.2.2
                                    linarith only [hlam, p8221_0]
                            · linarith only [h0, h8170, h8180, h8182, h8183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h8254 | h8254
                            · linarith only [h0, h8171, h8174, h8182, h8254, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h8256 | h8256
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h8257 | h8257
                                · rcases h1bigk with h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c | h8258c
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h0, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h6794, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h7647, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h7647, h8176, h8179, hc12, hlam, hphi, ht01, ht0b, ht5b, p8258_1, u5ehi1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8170, h8180, h8254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h6794, hc01, hc12, hlam, hphi, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h7647, h8170, h8180, h8254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    rcases p8258_3 (m.d 0 1) (by simp) with h8268 | h8268
                                    · linarith only [h0, h8268, hlam]
                                    · linarith only [h8170, h8268, hlam]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8170, h8180, h8254, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8176, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h7647, h8170, h8176, h8180, h8254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    rcases p8258_3 (m.d 0 1) (by simp) with h8275 | h8275
                                    · linarith only [h6794, h8275, hlam]
                                    · linarith only [h8170, h8275, hlam]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8170, h8180, h8254, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8177, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8179, hlam, p8258_1]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    rcases p8258_3 (m.d 0 1) (by simp) with h8282 | h8282
                                    · linarith only [h7647, h8282, hlam]
                                    · linarith only [h8170, h8282, hlam]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8170, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8178, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8180, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [h8181, hlam, p8258_0]
                                  · have p8258_0 := h8258c.1
                                    have p8258_1 := h8258c.2.1
                                    have p8258_2 := h8258c.2.2.1
                                    have p8258_3 := h8258c.2.2.2
                                    linarith only [hlam, p8258_0]
                                · linarith only [h0, h8172, h8182, h8256, h8257, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h8291 | h8291
                                · rcases h1bigk with h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h0, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h6794, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h7647, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h7647, h8176, h8179, hc12, hlam, hphi, ht01, ht0b, ht5b, p8292_1, u5ehi1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8170, h8180, h8256, h8291, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h6794, hc01, hc12, hlam, hphi, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h7647, h8170, h8180, h8256, h8291, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    rcases p8292_3 (m.d 0 1) (by simp) with h8302 | h8302
                                    · linarith only [h0, h8302, hlam]
                                    · linarith only [h8170, h8302, hlam]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8170, h8180, h8182, h8256, h8291, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8176, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h7647, h8170, h8176, h8180, h8182, h8256, h8291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    rcases p8292_3 (m.d 0 1) (by simp) with h8309 | h8309
                                    · linarith only [h6794, h8309, hlam]
                                    · linarith only [h8170, h8309, hlam]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8170, h8180, h8182, h8256, h8291, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8177, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8179, hlam, p8292_1]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    rcases p8292_3 (m.d 0 1) (by simp) with h8316 | h8316
                                    · linarith only [h7647, h8316, hlam]
                                    · linarith only [h8170, h8316, hlam]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8170, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8178, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8180, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [h8181, hlam, p8292_0]
                                  · have p8292_0 := h8292c.1
                                    have p8292_1 := h8292c.2.1
                                    have p8292_2 := h8292c.2.2.1
                                    have p8292_3 := h8292c.2.2.2
                                    linarith only [hlam, p8292_0]
                                · linarith only [h7647, h8170, h8176, h8179, h8181, h8182, h8291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h7647, h8170, h8181, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h7647, h8170, h8178, h8179, h8180, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h6794, h8170, h8178, h8179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h8170, h8178, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h6794, h8170, h8176, h8177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h8170, h8176, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h7647, h8170, h8175, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8332 | h8332
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8333 | h8333
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8334 | h8334
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8335 | h8335
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8336 | h8336
                    · linarith only [h6794, h8170, h8174, h8333, h8336, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · linarith only [h6794, h8170, h8335, h8336, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h8170, h8335, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h6794, h8170, h8172, h8333, h8334, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h8170, h8171, h8333, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h6794, h8170, h8174, h8332, hlam]
        · linarith only [h0, h8170, h8173, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8344 | h8344
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8345 | h8345
          · linarith only [h8171, h8172, h8345, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8347 | h8347
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8348 | h8348
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8349 | h8349
                · linarith only [h6794, h8170, h8171, h8172, h8349, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h8170, h8349, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h8170, h8171, h8348, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h0, h8170, h8172, h8347, hlam]
        · linarith only [h6794, h8170, h8171, h8344, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8355 | h8355
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8356 | h8356
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8357 | h8357
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8358 | h8358
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8359 | h8359
              · linarith only [h8171, h8356, h8359, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h8170, h8359, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h7647, h8170, h8358, hlam]
          · linarith only [h8171, h8355, h8357, hlam]
        · linarith only [h7647, h8170, h8355, h8356, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8365 | h8365
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8366 | h8366
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8367 | h8367
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8368 | h8368
              · linarith only [h0, h8170, h8171, h8368, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h8170, h8368, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h8170, h8355, h8367, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8372 | h8372
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8373 | h8373
              · linarith only [h0, h8170, h8171, h8373, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h8170, h8373, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h7647, h8170, h8372, hlam]
        · linarith only [h0, h8170, h8365, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s10 m hb1 hb2 hb4 hb5 h0 h6794 h7647 h8170

set_option maxHeartbeats 9558000 in
set_option maxHeartbeats 9558000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6794 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h6794 := hg6794
  rcases m.htr 0 1 4 (by decide) (by decide) with h7647 | h7647
  · rcases m.htr 0 1 5 (by decide) (by decide) with h7648 | h7648
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7649 | h7649
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7650 | h7650
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7651 | h7651
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7652 | h7652
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7653 | h7653
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7654 | h7654
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7655 | h7655
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7656 | h7656
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7657 | h7657
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7658 | h7658
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7659 | h7659
                          · linarith only [h6794, h7647, h7659, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7661 | h7661
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7662 | h7662
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7663 | h7663
                                · linarith only [h7655, h7659, h7663, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7665 | h7665
                                  · linarith only [h7655, h7659, h7661, h7665, hlam]
                                  · rcases h1bigk with h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c | h7667c
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h0, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h6794, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      rcases p7667_3 (m.d 0 1) (by simp) with h7671 | h7671
                                      · rcases p7667_3 (m.d 1 2) (by simp) with h7672 | h7672
                                        · rcases p7667_3 (m.d 1 3) (by simp) with h7673 | h7673
                                          · rcases p7667_3 (m.d 1 4) (by simp) with h7674 | h7674
                                            · linarith only [h7674, hlam, p7667_0]
                                            · rcases p7667_3 (m.d 1 5) (by simp) with h7676 | h7676
                                              · linarith only [h7648, h7676, hlam]
                                              · linarith only [h7659, h7676, hlam]
                                          · linarith only [h7657, h7673, hlam]
                                        · linarith only [h7655, h7672, hlam]
                                      · linarith only [h7671, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h6794, h7654, h7656, h7662, hc12, hlam, hphi, ht01, ht0b, ht5b, p7667_1, u5ehi3]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7647, h7653, h7659, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h6794, h7647, h7653, h7655, h7659, h7661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h0, h7647, h7653, h7659, hlam, p7667_2]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      rcases p7667_3 (m.d 0 1) (by simp) with h7687 | h7687
                                      · linarith only [h0, h7687, hlam]
                                      · linarith only [h7648, h7687, hlam]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7647, h7653, h7654, h7655, h7659, h7661, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7654, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h6794, h7647, h7653, h7659, hlam, p7667_2]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      rcases p7667_3 (m.d 0 1) (by simp) with h7694 | h7694
                                      · linarith only [h6794, h7694, hlam]
                                      · linarith only [h7648, h7694, hlam]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7647, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7655, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7657, hlam, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7659, hlam, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7648, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7656, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h7658, hlam, p7667_0]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [h6794, h7648, h7655, h7661, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7667_1]
                                    · have p7667_0 := h7667c.1
                                      have p7667_1 := h7667c.2.1
                                      have p7667_2 := h7667c.2.2.1
                                      have p7667_3 := h7667c.2.2.2
                                      linarith only [hlam, p7667_0]
                              · linarith only [h6794, h7647, h7653, h7654, h7658, h7659, h7661, h7662, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h6794, h7647, h7653, h7654, h7657, h7659, h7661, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6794, h7647, h7653, h7658, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h6794, h7647, h7653, h7657, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h0, h7647, h7653, h7656, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h6794, h7647, h7653, h7654, h7655, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h7647, h7653, h7654, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7714 | h7714
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7715 | h7715
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7716 | h7716
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7717 | h7717
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7718 | h7718
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7719 | h7719
                          · linarith only [h6794, h7647, h7653, h7714, h7719, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7721 | h7721
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7722 | h7722
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7723 | h7723
                                · linarith only [h7647, h7653, h7715, h7723, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7725 | h7725
                                  · linarith only [h7649, h7653, h7721, h7725, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c | h7727c
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h0, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h6794, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      rcases p7727_3 (m.d 0 1) (by simp) with h7731 | h7731
                                      · rcases p7727_3 (m.d 1 2) (by simp) with h7732 | h7732
                                        · rcases p7727_3 (m.d 1 3) (by simp) with h7733 | h7733
                                          · rcases p7727_3 (m.d 1 4) (by simp) with h7734 | h7734
                                            · linarith only [h7734, hlam, p7727_0]
                                            · rcases p7727_3 (m.d 1 5) (by simp) with h7736 | h7736
                                              · linarith only [h7648, h7736, hlam]
                                              · linarith only [h7719, h7736, hlam]
                                          · linarith only [h7717, h7733, hlam]
                                        · linarith only [h7715, h7732, hlam]
                                      · linarith only [h7731, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h6794, h7714, h7716, h7722, hc12, hlam, hphi, ht01, ht0b, ht5b, p7727_1, u5ehi3]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7648, h7716, h7722, hc12, hlam, hphi, ht01, ht0b, ht5b, p7727_1, u5ehi3]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h6794, hc01, hc12, hlam, hphi, p7727_1]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      rcases p7727_3 (m.d 0 1) (by simp) with h7746 | h7746
                                      · linarith only [h0, h7746, hlam]
                                      · linarith only [h7647, h7746, hlam]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      rcases p7727_3 (m.d 0 1) (by simp) with h7749 | h7749
                                      · linarith only [h0, h7749, hlam]
                                      · linarith only [h7648, h7749, hlam]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7648, h7714, h7716, h7722, hc12, hlam, hphi, ht01, ht0b, ht5b, p7727_1, u5ehi3]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7714, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      rcases p7727_3 (m.d 0 1) (by simp) with h7755 | h7755
                                      · linarith only [h6794, h7755, hlam]
                                      · linarith only [h7647, h7755, hlam]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      rcases p7727_3 (m.d 0 1) (by simp) with h7758 | h7758
                                      · linarith only [h6794, h7758, hlam]
                                      · linarith only [h7648, h7758, hlam]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7647, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7715, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7717, hlam, p7727_1]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7719, hlam, p7727_1]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7648, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7716, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h7718, hlam, p7727_0]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [h0, h7648, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7727_1]
                                    · have p7727_0 := h7727c.1
                                      have p7727_1 := h7727c.2.1
                                      have p7727_2 := h7727c.2.2.1
                                      have p7727_3 := h7727c.2.2.2
                                      linarith only [hlam, p7727_0]
                              · linarith only [h6794, h7648, h7714, h7718, h7721, h7722, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7772 | h7772
                              · linarith only [h7652, h7721, h7772, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7774 | h7774
                                · linarith only [h6794, h7648, h7653, h7714, h7717, h7719, h7721, h7774, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7776 | h7776
                                  · linarith only [h7647, h7653, h7717, h7776, hlam]
                                  · rcases h1bigk with h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c | h7778c
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h0, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h6794, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h6794, h7714, h7717, h7721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h6794, h7714, hc12, hlam, hphi, ht01, ht0b, ht5b, p7778_1, u5ehi1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7647, h7717, h7721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h6794, hc01, hc12, hlam, hphi, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      rcases p7778_3 (m.d 0 1) (by simp) with h7787 | h7787
                                      · linarith only [h0, h7787, hlam]
                                      · linarith only [h7647, h7787, hlam]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      rcases p7778_3 (m.d 0 1) (by simp) with h7790 | h7790
                                      · linarith only [h0, h7790, hlam]
                                      · linarith only [h7648, h7790, hlam]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7648, hc13, hlam, hphi, ht01, ht0b, ht5b, p7778_1, u5ehi1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7714, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      rcases p7778_3 (m.d 0 1) (by simp) with h7796 | h7796
                                      · linarith only [h6794, h7796, hlam]
                                      · linarith only [h7647, h7796, hlam]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      rcases p7778_3 (m.d 0 1) (by simp) with h7799 | h7799
                                      · linarith only [h6794, h7799, hlam]
                                      · linarith only [h7648, h7799, hlam]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7647, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7715, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7717, hlam, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7719, hlam, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7648, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7716, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7718, hlam, p7778_0]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [h7648, h7717, h7721, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7778_1]
                                    · have p7778_0 := h7778c.1
                                      have p7778_1 := h7778c.2.1
                                      have p7778_2 := h7778c.2.2.1
                                      have p7778_3 := h7778c.2.2.2
                                      linarith only [hlam, p7778_0]
                        · linarith only [h6794, h7648, h7718, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h6794, h7648, h7716, h7717, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h7648, h7716, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h6794, h7648, h7714, h7715, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h7648, h7714, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h6794, h7647, h7652, hlam]
          · linarith only [h0, h7648, h7651, hlam]
        · linarith only [h6794, h7647, h7649, h7650, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7820 | h7820
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7821 | h7821
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7822 | h7822
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7823 | h7823
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7824 | h7824
                · linarith only [h7649, h7821, h7824, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h7647, h7823, h7824, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7827 | h7827
                · linarith only [h0, h7648, h7649, h7827, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h7648, h7827, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h7647, h7649, h7822, hlam]
          · linarith only [h0, h7648, h7821, hlam]
        · linarith only [h0, h7647, h7820, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7833 | h7833
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7834 | h7834
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7835 | h7835
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7836 | h7836
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7837 | h7837
              · linarith only [h7647, h7648, h7837, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7839 | h7839
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7840 | h7840
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7841 | h7841
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7842 | h7842
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7843 | h7843
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7844 | h7844
                          · linarith only [h7647, h7648, h7837, h7839, h7843, h7844, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7846 | h7846
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7847 | h7847
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7848 | h7848
                                · linarith only [h7647, h7648, h7840, h7844, h7848, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7850 | h7850
                                  · linarith only [h7648, h7833, h7844, h7846, h7850, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                  · rcases h1bigk with h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c | h7852c
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h0, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h6794, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7648, h7840, h7844, h7846, hc34, hc45, hlam, hphi, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7648, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      rcases p7852_3 (m.d 0 1) (by simp) with h7858 | h7858
                                      · linarith only [h7858, hlam, p7852_0]
                                      · rcases p7852_3 (m.d 1 2) (by simp) with h7860 | h7860
                                        · rcases p7852_3 (m.d 1 3) (by simp) with h7861 | h7861
                                          · linarith only [h7839, h7861, hlam]
                                          · linarith only [h6794, h7861, hlam]
                                        · linarith only [h7860, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h6794, hc01, hc12, hlam, hphi, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      rcases p7852_3 (m.d 0 1) (by simp) with h7867 | h7867
                                      · linarith only [h0, h7867, hlam]
                                      · linarith only [h7647, h7867, hlam]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7648, hc01, hc12, hlam, hphi, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      rcases p7852_3 (m.d 0 1) (by simp) with h7871 | h7871
                                      · linarith only [h7871, hlam, p7852_0]
                                      · rcases p7852_3 (m.d 1 2) (by simp) with h7873 | h7873
                                        · rcases p7852_3 (m.d 1 3) (by simp) with h7874 | h7874
                                          · rcases p7852_3 (m.d 1 4) (by simp) with h7875 | h7875
                                            · linarith only [h7842, h7875, hlam]
                                            · rcases p7852_3 (m.d 1 5) (by simp) with h7877 | h7877
                                              · linarith only [h7843, h7877, hlam]
                                              · linarith only [h7648, h7877, hlam]
                                          · linarith only [h7874, hlam, p7852_0]
                                        · linarith only [h0, h7873, hlam]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7839, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      rcases p7852_3 (m.d 0 1) (by simp) with h7884 | h7884
                                      · linarith only [h6794, h7884, hlam]
                                      · linarith only [h7647, h7884, hlam]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7647, h7648, h7840, h7846, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7647, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7840, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7842, hlam, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7844, hlam, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7647, h7840, h7844, h7846, hc34, hc45, hlam, hphi, p7852_1]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7841, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [h7843, hlam, p7852_0]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      rcases p7852_3 (m.d 0 1) (by simp) with h7896 | h7896
                                      · linarith only [h7648, h7896, hlam]
                                      · linarith only [h7647, h7896, hlam]
                                    · have p7852_0 := h7852c.1
                                      have p7852_1 := h7852c.2.1
                                      have p7852_2 := h7852c.2.2.1
                                      have p7852_3 := h7852c.2.2.2
                                      linarith only [hlam, p7852_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7900 | h7900
                                · linarith only [h0, h7647, h7648, h7840, h7844, h7900, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7902 | h7902
                                  · linarith only [h7648, h7839, h7843, h7844, h7846, h7847, h7902, hc01, hc12, hlam, hphi]
                                  · rcases h1bigk with h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c | h7904c
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h0, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h6794, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7648, h7840, h7844, h7846, hc34, hc45, hlam, hphi, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7648, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      rcases p7904_3 (m.d 0 1) (by simp) with h7910 | h7910
                                      · linarith only [h7910, hlam, p7904_0]
                                      · rcases p7904_3 (m.d 1 2) (by simp) with h7912 | h7912
                                        · rcases p7904_3 (m.d 1 3) (by simp) with h7913 | h7913
                                          · linarith only [h7839, h7913, hlam]
                                          · linarith only [h6794, h7913, hlam]
                                        · linarith only [h7912, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7843, h7847, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      rcases p7904_3 (m.d 0 1) (by simp) with h7919 | h7919
                                      · linarith only [h0, h7919, hlam]
                                      · linarith only [h7647, h7919, hlam]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7648, hc01, hc12, hlam, hphi, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      rcases p7904_3 (m.d 0 1) (by simp) with h7923 | h7923
                                      · linarith only [h7923, hlam, p7904_0]
                                      · rcases p7904_3 (m.d 1 2) (by simp) with h7925 | h7925
                                        · rcases p7904_3 (m.d 1 3) (by simp) with h7926 | h7926
                                          · rcases p7904_3 (m.d 1 4) (by simp) with h7927 | h7927
                                            · linarith only [h7842, h7927, hlam]
                                            · rcases p7904_3 (m.d 1 5) (by simp) with h7929 | h7929
                                              · linarith only [h7843, h7929, hlam]
                                              · linarith only [h7648, h7929, hlam]
                                          · linarith only [h7926, hlam, p7904_0]
                                        · linarith only [h0, h7925, hlam]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7839, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      rcases p7904_3 (m.d 0 1) (by simp) with h7936 | h7936
                                      · linarith only [h6794, h7936, hlam]
                                      · linarith only [h7647, h7936, hlam]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7647, h7648, h7840, h7846, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7647, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7840, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7842, hlam, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7844, hlam, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7647, h7840, h7844, h7846, hc34, hc45, hlam, hphi, p7904_1]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7841, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [h7843, hlam, p7904_0]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      rcases p7904_3 (m.d 0 1) (by simp) with h7948 | h7948
                                      · linarith only [h7648, h7948, hlam]
                                      · linarith only [h7647, h7948, hlam]
                                    · have p7904_0 := h7904c.1
                                      have p7904_1 := h7904c.2.1
                                      have p7904_2 := h7904c.2.2.1
                                      have p7904_3 := h7904c.2.2.2
                                      linarith only [hlam, p7904_0]
                            · linarith only [h7647, h7648, h7842, h7844, h7846, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7953 | h7953
                          · linarith only [h6794, h7647, h7843, h7953, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7955 | h7955
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7956 | h7956
                              · linarith only [h6794, h7843, h7956, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7958 | h7958
                                · linarith only [h6794, h7647, h7840, h7843, h7953, h7958, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7960 | h7960
                                  · linarith only [h6794, h7647, h7840, h7843, h7953, h7955, h7960, hlam]
                                  · linarith only [h6794, h7647, h7840, h7843, h7955, h7960, hc34, hc45, hlam, hphi]
                            · linarith only [h6794, h7836, h7843, h7955, hc23, hc35, hlam, hphi]
                      · linarith only [h6794, h7647, h7836, h7842, hlam]
                    · linarith only [h0, h7835, h7841, hlam]
                  · linarith only [h0, h7834, h7840, hlam]
                · linarith only [h0, h7833, h7839, hlam]
            · linarith only [h6794, h7647, h7836, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7969 | h7969
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7970 | h7970
              · linarith only [h0, h7647, h7835, h7970, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7972 | h7972
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7973 | h7973
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7974 | h7974
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7975 | h7975
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7976 | h7976
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7977 | h7977
                          · linarith only [h6794, h7647, h7833, h7835, h7970, h7974, h7977, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7979 | h7979
                            · linarith only [h7833, h7835, h7974, h7979, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h7833, h7835, h7969, h7974, h7979, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7982 | h7982
                          · linarith only [h6794, h7647, h7833, h7835, h7974, h7982, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7984 | h7984
                            · linarith only [h7833, h7835, h7974, h7984, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h7833, h7835, h7969, h7974, h7984, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h6794, h7647, h7969, h7975, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7988 | h7988
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7989 | h7989
                        · linarith only [h7972, h7974, h7989, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7991 | h7991
                          · linarith only [h6794, h7647, h7989, h7991, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7993 | h7993
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7994 | h7994
                              · linarith only [h6794, h7833, h7989, h7994, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7996 | h7996
                                · linarith only [h6794, h7647, h7972, h7973, h7974, h7991, h7996, hlam]
                                · linarith only [h6794, h7647, h7972, h7973, h7974, h7993, h7996, hc34, hc45, hlam, hphi]
                            · linarith only [h6794, h7647, h7972, h7974, h7988, h7993, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h6794, h7969, h7988, hlam]
                  · linarith only [h0, h7834, h7973, hlam]
                · linarith only [h0, h7833, h7972, hlam]
            · linarith only [h6794, h7647, h7969, hlam]
        · linarith only [h0, h7647, h7834, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h8005 | h8005
        · rcases m.htr 0 2 5 (by decide) (by decide) with h8006 | h8006
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8007 | h8007
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8008 | h8008
              · linarith only [h7647, h7648, h8008, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8010 | h8010
                · linarith only [h7833, h8006, h8010, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8012 | h8012
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8013 | h8013
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8014 | h8014
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8015 | h8015
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8016 | h8016
                          · linarith only [h0, h7647, h8008, h8010, h8016, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8018 | h8018
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8019 | h8019
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8020 | h8020
                                · linarith only [h7647, h7648, h8012, h8016, h8020, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8022 | h8022
                                  · linarith only [h7647, h7648, h8007, h8016, h8022, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c | h8024c
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h0, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h6794, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h7648, h8010, h8012, h8013, h8018, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h7648, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8010, hc01, hc23, hlam, hphi, ht12, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8010, hlam, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      rcases p8024_3 (m.d 0 1) (by simp) with h8033 | h8033
                                      · linarith only [h0, h8033, hlam]
                                      · linarith only [h7647, h8033, hlam]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8010, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8024_1, u5ehi1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      rcases p8024_3 (m.d 0 1) (by simp) with h8037 | h8037
                                      · linarith only [h8037, hlam, p8024_0]
                                      · rcases p8024_3 (m.d 1 2) (by simp) with h8039 | h8039
                                        · linarith only [h8010, h8039, hlam]
                                        · linarith only [h0, h8039, hlam]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h0, h7647, h8010, h8012, h8018, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      rcases p8024_3 (m.d 0 1) (by simp) with h8044 | h8044
                                      · linarith only [h6794, h8044, hlam]
                                      · linarith only [h7647, h8044, hlam]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h7647, h7648, h8012, h8018, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h7647, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8012, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8014, hlam, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8016, hlam, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h7647, h8012, h8016, h8018, hc34, hc45, hlam, hphi, p8024_1]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8013, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [h8015, hlam, p8024_0]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      rcases p8024_3 (m.d 0 1) (by simp) with h8056 | h8056
                                      · linarith only [h7648, h8056, hlam]
                                      · linarith only [h7647, h8056, hlam]
                                    · have p8024_0 := h8024c.1
                                      have p8024_1 := h8024c.2.1
                                      have p8024_2 := h8024c.2.2.1
                                      have p8024_3 := h8024c.2.2.2
                                      linarith only [hlam, p8024_0]
                              · linarith only [h0, h7647, h8010, h8012, h8018, h8019, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h8010, h8018, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h8010, h8013, h8015, hlam]
                      · linarith only [h6794, h8007, h8014, hlam]
                    · linarith only [h0, h6794, h7647, h7833, h8006, h8012, h8013, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h8005, h8012, hlam]
            · linarith only [h6794, h7647, h8007, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8067 | h8067
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8068 | h8068
              · linarith only [h0, h7647, h8006, h8068, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8070 | h8070
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8071 | h8071
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8072 | h8072
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8073 | h8073
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8074 | h8074
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8075 | h8075
                          · linarith only [h0, h7647, h7833, h8068, h8070, h8075, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8077 | h8077
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8078 | h8078
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8079 | h8079
                                · linarith only [h0, h7647, h8006, h8071, h8072, h8075, h8079, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8081 | h8081
                                  · linarith only [h0, h7647, h8006, h8071, h8072, h8075, h8077, h8081, hlam]
                                  · rcases h1bigk with h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c | h8083c
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h6794, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, h8006, h8070, h8078, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h7648, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      rcases p8083_3 (m.d 0 1) (by simp) with h8089 | h8089
                                      · linarith only [h8089, hlam, p8083_0]
                                      · rcases p8083_3 (m.d 1 2) (by simp) with h8091 | h8091
                                        · rcases p8083_3 (m.d 1 3) (by simp) with h8092 | h8092
                                          · linarith only [h8070, h8092, hlam]
                                          · linarith only [h6794, h8092, hlam]
                                        · linarith only [h8091, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, h8006, h8072, h8074, hc01, hc12, hlam, hphi, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, h7647, h7833, h8070, hlam, p8083_2]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, h7647, h8006, h8071, h8072, h8077, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      rcases p8083_3 (m.d 0 1) (by simp) with h8100 | h8100
                                      · linarith only [h8100, hlam, p8083_0]
                                      · rcases p8083_3 (m.d 1 2) (by simp) with h8102 | h8102
                                        · rcases p8083_3 (m.d 1 3) (by simp) with h8103 | h8103
                                          · rcases p8083_3 (m.d 1 4) (by simp) with h8104 | h8104
                                            · linarith only [h8073, h8104, hlam]
                                            · rcases p8083_3 (m.d 1 5) (by simp) with h8106 | h8106
                                              · linarith only [h8074, h8106, hlam]
                                              · linarith only [h7648, h8106, hlam]
                                          · linarith only [h8103, hlam, p8083_0]
                                        · linarith only [h0, h8102, hlam]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8070, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      rcases p8083_3 (m.d 0 1) (by simp) with h8113 | h8113
                                      · linarith only [h6794, h8113, hlam]
                                      · linarith only [h7647, h8113, hlam]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h0, h7647, h8006, h8071, h8072, h8077, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h7647, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8071, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8073, hlam, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8075, hlam, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h7647, h8071, h8075, h8077, hc34, hc45, hlam, hphi, p8083_1]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8072, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [h8074, hlam, p8083_0]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      rcases p8083_3 (m.d 0 1) (by simp) with h8125 | h8125
                                      · linarith only [h7648, h8125, hlam]
                                      · linarith only [h7647, h8125, hlam]
                                    · have p8083_0 := h8083c.1
                                      have p8083_1 := h8083c.2.1
                                      have p8083_2 := h8083c.2.2.1
                                      have p8083_3 := h8083c.2.2.2
                                      linarith only [hlam, p8083_0]
                              · linarith only [h0, h7647, h7833, h8070, h8071, h8074, h8077, h8078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h7647, h7833, h8067, h8071, h8077, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8131 | h8131
                          · linarith only [h0, h7647, h7833, h8131, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8133 | h8133
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8134 | h8134
                              · linarith only [h8070, h8074, h8134, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8136 | h8136
                                · linarith only [h0, h7647, h7833, h8070, h8071, h8074, h8131, h8136, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8138 | h8138
                                  · linarith only [h0, h7647, h7833, h8071, h8072, h8131, h8133, h8134, h8138, hlam]
                                  · linarith only [h0, h7647, h7833, h8070, h8071, h8074, h8133, h8138, hc34, hc45, hlam, hphi]
                            · linarith only [h7833, h8067, h8133, hlam]
                      · linarith only [h0, h7647, h7833, h8067, h8070, h8073, hlam]
                    · linarith only [h0, h7647, h7833, h8070, h8071, h8072, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h7647, h7833, h8070, h8071, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8145 | h8145
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8146 | h8146
                    · linarith only [h0, h7647, h8006, h8070, h8145, h8146, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8148 | h8148
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8149 | h8149
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8150 | h8150
                          · linarith only [h0, h7647, h8070, h8150, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8152 | h8152
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8153 | h8153
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8154 | h8154
                                · linarith only [h0, h7647, h8145, h8146, h8150, h8154, hlam]
                                · linarith only [h0, h7647, h8146, h8154, hc14, hc45, hlam, hphi]
                              · linarith only [h8070, h8149, h8153, hlam]
                            · linarith only [h6794, h8067, h8070, h8152, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8159 | h8159
                          · linarith only [h0, h7647, h8159, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8161 | h8161
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8162 | h8162
                              · linarith only [h0, h7647, h8070, h8145, h8149, h8161, h8162, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h7647, h8070, h8145, h8161, h8162, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h7647, h8070, h8145, h8161, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h7647, h8067, h8070, h8148, hlam]
                  · linarith only [h0, h8005, h8145, hlam]
            · linarith only [h6794, h7647, h8067, hlam]
        · linarith only [h0, h7647, h8005, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s9 m hb1 hb2 hb4 hb5 h0 h6794 h7647

end R2N4
