import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S0
import Jsp000404.R1LeavesN7_40S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h1241 | h1241
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h927 | h927
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x0 m hb1 hb2 hb4 hb5 hg0 h927
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1 m hb1 hb2 hb4 hb5 hg0 h927

set_option maxHeartbeats 6934000 in
set_option maxHeartbeats 6934000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h0, h12, h14, h17, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                    · linarith only [h0, h14, h24, h26, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                      · linarith only [h10, h14, h28, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h1bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h25, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 1) (by simp) with h33 | h33
                                          · rcases p30_3 (m.d 1 2) (by simp) with h34 | h34
                                            · linarith only [h0, h34, hlam]
                                            · linarith only [h34, h9, hlam]
                                          · linarith only [h33, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 1) (by simp) with h38 | h38
                                          · rcases p30_3 (m.d 1 2) (by simp) with h39 | h39
                                            · linarith only [h0, h39, hlam]
                                            · linarith only [h10, h39, hlam]
                                          · linarith only [h38, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 1) (by simp) with h43 | h43
                                          · rcases p30_3 (m.d 1 2) (by simp) with h44 | h44
                                            · linarith only [h0, h44, hlam]
                                            · linarith only [h11, h44, hlam]
                                          · linarith only [h43, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h25, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h11, h26, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h1, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h9, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h1, h10, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h11, h26, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h10, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h12, hlam, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h14, hlam, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h2, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h11, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h13, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p30_1, u2ehi3]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                  · linarith only [h0, h13, h25, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h24, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h12, h13, h70, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h73 | h73
                                  · linarith only [h0, h13, h73, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                                    · linarith only [h10, h70, h75, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                                      · linarith only [h10, h70, h72, h77, hc23, hlam, hphi, u2ehi3]
                                      · rcases h1bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi4]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 1) (by simp) with h82 | h82
                                          · rcases p79_3 (m.d 1 2) (by simp) with h83 | h83
                                            · linarith only [h0, h83, hlam]
                                            · linarith only [h83, h9, hlam]
                                          · linarith only [h82, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 1) (by simp) with h87 | h87
                                          · rcases p79_3 (m.d 1 2) (by simp) with h88 | h88
                                            · linarith only [h0, h88, hlam]
                                            · linarith only [h10, h88, hlam]
                                          · linarith only [h87, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          rcases p79_3 (m.d 0 1) (by simp) with h92 | h92
                                          · rcases p79_3 (m.d 1 2) (by simp) with h93 | h93
                                            · linarith only [h0, h93, hlam]
                                            · linarith only [h11, h93, hlam]
                                          · linarith only [h92, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h10, h12, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h10, h12, h13, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h1, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h9, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h10, h13, h6, h77, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h13, hlam, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h10, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h12, hlam, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h70, hlam, p79_1]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h2, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h11, hlam, p79_0]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h2, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi2]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [h0, h10, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p79_1, u2ehi3]
                                        · have p79_0 := h79c.1
                                          have p79_1 := h79c.2.1
                                          have p79_2 := h79c.2.2.1
                                          have p79_3 := h79c.2.2.2
                                          linarith only [hlam, p79_0]
                                · linarith only [h1, h12, h72, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                                · linarith only [h0, h10, h12, h120, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                                      · rcases h1bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h122, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 1) (by simp) with h128 | h128
                                          · rcases p125_3 (m.d 1 2) (by simp) with h129 | h129
                                            · linarith only [h0, h129, hlam]
                                            · linarith only [h129, h9, hlam]
                                          · linarith only [h128, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 1) (by simp) with h133 | h133
                                          · rcases p125_3 (m.d 1 2) (by simp) with h134 | h134
                                            · linarith only [h0, h134, hlam]
                                            · linarith only [h10, h134, hlam]
                                          · linarith only [h133, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          rcases p125_3 (m.d 0 1) (by simp) with h138 | h138
                                          · rcases p125_3 (m.d 1 2) (by simp) with h139 | h139
                                            · linarith only [h0, h139, hlam]
                                            · linarith only [h11, h139, hlam]
                                          · linarith only [h138, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h122, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h12, h122, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h1, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h9, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h12, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h1, h11, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h12, h3, h6, hlam, p125_1]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h10, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h12, h122, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h0, h11, h12, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi4]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h2, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h11, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h118, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [h119, hlam, p125_0]
                                        · have p125_0 := h125c.1
                                          have p125_1 := h125c.2.1
                                          have p125_2 := h125c.2.2.1
                                          have p125_3 := h125c.2.2.2
                                          linarith only [hlam, p125_0]
                                      · linarith only [h0, h12, h122, h124, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                    · linarith only [h0, h118, h119, h12, h120, h122, h123, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                  · linarith only [h0, h118, h12, h122, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h118, h119, h12, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                                · linarith only [h12, h168, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                                  · linarith only [h118, h170, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                      · rcases h1bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 1) (by simp) with h177 | h177
                                          · rcases p174_3 (m.d 1 2) (by simp) with h178 | h178
                                            · linarith only [h0, h178, hlam]
                                            · linarith only [h178, h9, hlam]
                                          · linarith only [h177, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 1) (by simp) with h182 | h182
                                          · rcases p174_3 (m.d 1 2) (by simp) with h183 | h183
                                            · linarith only [h0, h183, hlam]
                                            · linarith only [h10, h183, hlam]
                                          · linarith only [h182, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          rcases p174_3 (m.d 0 1) (by simp) with h187 | h187
                                          · rcases p174_3 (m.d 1 2) (by simp) with h188 | h188
                                            · linarith only [h0, h188, hlam]
                                            · linarith only [h11, h188, hlam]
                                          · linarith only [h187, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h118, h167, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h118, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h1, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h9, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h12, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h118, hlam, p174_1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi1]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h10, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h0, h10, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h118, h12, h3, h6, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h2, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h11, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h2, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, u2ehi2]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [h167, hlam, p174_0]
                                        · have p174_0 := h174c.1
                                          have p174_1 := h174c.2.1
                                          have p174_2 := h174c.2.2.1
                                          have p174_3 := h174c.2.2.2
                                          linarith only [hlam, p174_0]
                                      · linarith only [h0, h10, h12, h172, h173, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h12, h167, h168, h172, hc34, hlam, hphi, ht23, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                                · linarith only [h12, h214, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h216 | h216
                                  · linarith only [h118, h216, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h218 | h218
                                    · linarith only [h0, h10, h167, h218, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                                      · linarith only [h12, h167, h220, h9, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h12, h220, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h11, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
                      · linarith only [h225, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h0, h227, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h230 | h230
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h234 | h234
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                                      · rcases h1bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          rcases p236_3 (m.d 0 1) (by simp) with h238 | h238
                                          · rcases p236_3 (m.d 1 2) (by simp) with h239 | h239
                                            · linarith only [h239, hlam, p236_0]
                                            · rcases p236_3 (m.d 1 3) (by simp) with h241 | h241
                                              · linarith only [h1, h241, hlam]
                                              · linarith only [h241, h9, hlam]
                                          · linarith only [h238, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h229, h235, hc01, hc45, hlam, hphi, ht0b, ht5b, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          rcases p236_3 (m.d 0 1) (by simp) with h246 | h246
                                          · rcases p236_3 (m.d 1 2) (by simp) with h247 | h247
                                            · linarith only [h0, h247, hlam]
                                            · rcases p236_3 (m.d 1 3) (by simp) with h249 | h249
                                              · linarith only [h1, h249, hlam]
                                              · linarith only [h229, h249, hlam]
                                          · linarith only [h246, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          rcases p236_3 (m.d 0 1) (by simp) with h253 | h253
                                          · rcases p236_3 (m.d 1 2) (by simp) with h254 | h254
                                            · linarith only [h0, h254, hlam]
                                            · rcases p236_3 (m.d 1 3) (by simp) with h256 | h256
                                              · linarith only [h1, h256, hlam]
                                              · linarith only [h230, h256, hlam]
                                          · linarith only [h253, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h9, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h225, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h227, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h1, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h231, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h3, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi2]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h225, hc24, hlam, hphi, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h229, hlam, p236_1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h0, h227, h229, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h2, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p236_1, u2ehi1]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h230, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [h231, hlam, p236_0]
                                        · have p236_0 := h236c.1
                                          have p236_1 := h236c.2.1
                                          have p236_2 := h236c.2.2.1
                                          have p236_3 := h236c.2.2.2
                                          linarith only [hlam, p236_0]
                                      · rcases h1bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          rcases p280_3 (m.d 0 1) (by simp) with h282 | h282
                                          · rcases p280_3 (m.d 1 2) (by simp) with h283 | h283
                                            · linarith only [h283, hlam, p280_0]
                                            · rcases p280_3 (m.d 1 3) (by simp) with h285 | h285
                                              · linarith only [h1, h285, hlam]
                                              · linarith only [h285, h9, hlam]
                                          · linarith only [h282, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h229, h231, h235, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h231, h235, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          rcases p280_3 (m.d 0 1) (by simp) with h291 | h291
                                          · rcases p280_3 (m.d 1 2) (by simp) with h292 | h292
                                            · linarith only [h0, h292, hlam]
                                            · rcases p280_3 (m.d 1 3) (by simp) with h294 | h294
                                              · linarith only [h1, h294, hlam]
                                              · linarith only [h230, h294, hlam]
                                          · linarith only [h291, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h0, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h9, hlam, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h225, hlam, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h227, hlam, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h1, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p280_1, u2ehi1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h0, h231, h235, h3, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h0, h227, h3, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p280_1, u2ehi1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h0, h3, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p280_1, u2ehi2]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h225, hc24, hlam, hphi, p280_1, u2ehi1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h229, hlam, p280_1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h227, h229, h9, hc23, hlam, hphi, p280_1, u2ehi1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h2, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p280_1, u2ehi1]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h230, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [h231, hlam, p280_0]
                                        · have p280_0 := h280c.1
                                          have p280_1 := h280c.2.1
                                          have p280_2 := h280c.2.2.1
                                          have p280_3 := h280c.2.2.2
                                          linarith only [hlam, p280_0]
                                    · linarith only [h0, h225, h234, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h233, h3, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h232, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                                    · linarith only [h0, h225, h231, h3, h321, h323, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h225, h323, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h1, h230, h322, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h3, h321, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                              · linarith only [h229, h230, h328, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                                  · linarith only [h0, h229, h230, h3, h331, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h331, h9, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h330, h9, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                                · linarith only [h0, h227, h229, h3, h335, h337, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h337, h6, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h229, h335, h336, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                                · linarith only [h229, h342, h9, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h342, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                                · linarith only [h0, h229, h3, h345, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h3, h345, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h348 | h348
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h353 | h353
                              · linarith only [h1, h351, h353, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h356 | h356
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h357 | h357
                                    · linarith only [h357, h4, h8, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                                      · linarith only [h0, h348, h355, h359, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h1bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h348, h356, h359, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p361_1]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          rcases p361_3 (m.d 0 1) (by simp) with h364 | h364
                                          · rcases p361_3 (m.d 1 2) (by simp) with h365 | h365
                                            · linarith only [h0, h365, hlam]
                                            · linarith only [h348, h365, hlam]
                                          · linarith only [h364, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          rcases p361_3 (m.d 0 1) (by simp) with h369 | h369
                                          · rcases p361_3 (m.d 1 2) (by simp) with h370 | h370
                                            · linarith only [h0, h370, hlam]
                                            · linarith only [h349, h370, hlam]
                                          · linarith only [h369, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          rcases p361_3 (m.d 0 1) (by simp) with h374 | h374
                                          · rcases p361_3 (m.d 1 2) (by simp) with h375 | h375
                                            · linarith only [h0, h375, hlam]
                                            · linarith only [h350, h375, hlam]
                                          · linarith only [h374, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, h348, h356, h357, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, h349, h353, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h1, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h348, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h1, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, h348, h349, h353, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h0, h2, h353, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi1]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h349, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h351, hlam, p361_1]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h353, hlam, p361_1]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h2, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h350, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h352, hlam, p361_0]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [h2, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p361_1, u2ehi3]
                                        · have p361_0 := h361c.1
                                          have p361_1 := h361c.2.1
                                          have p361_2 := h361c.2.2.1
                                          have p361_3 := h361c.2.2.2
                                          linarith only [hlam, p361_0]
                                  · linarith only [h0, h348, h352, h356, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h355, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                              · linarith only [h351, h352, h4, h401, h8, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                                  · linarith only [h0, h348, h352, h404, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                                    · linarith only [h349, h351, h352, h406, h7, h8, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                      · linarith only [h349, h351, h352, h403, h408, h7, h8, hc23, hlam, hphi, u2ehi3]
                                      · rcases h1bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h350, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi4]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          rcases p410_3 (m.d 0 1) (by simp) with h413 | h413
                                          · rcases p410_3 (m.d 1 2) (by simp) with h414 | h414
                                            · linarith only [h0, h414, hlam]
                                            · linarith only [h348, h414, hlam]
                                          · linarith only [h413, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          rcases p410_3 (m.d 0 1) (by simp) with h418 | h418
                                          · rcases p410_3 (m.d 1 2) (by simp) with h419 | h419
                                            · linarith only [h0, h419, hlam]
                                            · linarith only [h349, h419, hlam]
                                          · linarith only [h418, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          rcases p410_3 (m.d 0 1) (by simp) with h423 | h423
                                          · rcases p410_3 (m.d 1 2) (by simp) with h424 | h424
                                            · linarith only [h0, h424, hlam]
                                            · linarith only [h350, h424, hlam]
                                          · linarith only [h423, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, h349, h351, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi3]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, h349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi3]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, h350, h403, h404, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p410_1]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h1, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h348, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h349, h352, h7, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi3]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h352, hlam, p410_1]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, h351, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h349, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h351, hlam, p410_1]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h401, hlam, p410_1]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h2, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h350, hlam, p410_0]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h2, h348, h403, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi3]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [h0, h3, h349, h352, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi3]
                                        · have p410_0 := h410c.1
                                          have p410_1 := h410c.2.1
                                          have p410_2 := h410c.2.2.1
                                          have p410_3 := h410c.2.2.2
                                          linarith only [hlam, p410_0]
                                · linarith only [h403, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h348, h351, h6, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h348, h350, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h348, h349, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
                      · linarith only [h348, h452, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h4, h452, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h455, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h459 | h459
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h1, h461, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                              · linarith only [h1, h4, h455, h460, h463, h7, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h465 | h465
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
                                  · linarith only [h3, h466, h7, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h468 | h468
                                    · linarith only [h4, h455, h468, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h470 | h470
                                      · linarith only [h4, h455, h470, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h1bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h459, h465, h466, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h475 | h475
                                          · rcases p472_3 (m.d 1 2) (by simp) with h476 | h476
                                            · linarith only [h0, h476, hlam]
                                            · linarith only [h457, h476, hlam]
                                          · linarith only [h475, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h480 | h480
                                          · rcases p472_3 (m.d 1 2) (by simp) with h481 | h481
                                            · linarith only [h0, h481, hlam]
                                            · linarith only [h458, h481, hlam]
                                          · linarith only [h480, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          rcases p472_3 (m.d 0 1) (by simp) with h485 | h485
                                          · rcases p472_3 (m.d 1 2) (by simp) with h486 | h486
                                            · linarith only [h0, h486, hlam]
                                            · linarith only [h459, h486, hlam]
                                          · linarith only [h485, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, h457, h465, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, h458, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, h457, h461, h465, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h1, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h457, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h1, h458, h7, hc35, hlam, hphi, ht23, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h461, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h458, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h460, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h463, hlam, p472_1]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h2, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h459, hlam, p472_0]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h2, h457, h465, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [h2, h458, h470, h7, hc45, hlam, hphi, ht23, ht34, p472_1, u2ehi3]
                                        · have p472_0 := h472c.1
                                          have p472_1 := h472c.2.1
                                          have p472_2 := h472c.2.2.1
                                          have p472_3 := h472c.2.2.2
                                          linarith only [hlam, p472_0]
                                · linarith only [h465, h6, h7, hc23, hc35, hlam, hphi]
                          · linarith only [h457, h460, h6, h7, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h457, h459, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h457, h458, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h457, h7, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h515 | h515
                · rcases m.htr 0 4 5 (by decide) (by decide) with h516 | h516
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                          · linarith only [h1, h515, h520, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h523 | h523
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                                · linarith only [h2, h515, h519, h524, h6, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h526 | h526
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h528 | h528
                                      · rcases h1bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h518, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi3]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          rcases p529_3 (m.d 0 1) (by simp) with h532 | h532
                                          · rcases p529_3 (m.d 1 2) (by simp) with h533 | h533
                                            · linarith only [h0, h533, hlam]
                                            · linarith only [h517, h533, hlam]
                                          · linarith only [h532, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          rcases p529_3 (m.d 0 1) (by simp) with h537 | h537
                                          · rcases p529_3 (m.d 1 2) (by simp) with h538 | h538
                                            · linarith only [h0, h538, hlam]
                                            · linarith only [h518, h538, hlam]
                                          · linarith only [h537, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          rcases p529_3 (m.d 0 1) (by simp) with h542 | h542
                                          · rcases p529_3 (m.d 1 2) (by simp) with h543 | h543
                                            · linarith only [h0, h543, hlam]
                                            · linarith only [h519, h543, hlam]
                                          · linarith only [h542, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, h517, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi2]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, h517, h520, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi2]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, h519, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi4]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h1, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h517, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h520, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h1, h519, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi4]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi1]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h518, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h0, h517, h518, h526, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p529_1, u2ehi4]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h519, h520, hc34, hlam, hphi, ht23, p529_1, u2ehi4]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h2, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h519, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h522, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [h523, hlam, p529_0]
                                        · have p529_0 := h529c.1
                                          have p529_1 := h529c.2.1
                                          have p529_2 := h529c.2.2.1
                                          have p529_3 := h529c.2.2.2
                                          linarith only [hlam, p529_0]
                                      · linarith only [h2, h515, h519, h528, h6, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                    · linarith only [h516, h524, h526, h527, h6, hc34, hlam, hphi, ht23, u2ehi4]
                                  · linarith only [h515, h526, h6, hc23, hc34, hlam, hphi]
                              · linarith only [h516, h518, h523, h6, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h515, h522, h6, hc13, hc34, hlam, hphi]
                        · linarith only [h5, h515, h519, h6, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h517, h518, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h517, h6, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h515, h516, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h580 | h580
                          · linarith only [h1, h580, h6, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h582 | h582
                            · linarith only [h1, h515, h582, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h584 | h584
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                                · linarith only [h0, h4, h577, h585, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h587 | h587
                                  · linarith only [h1, h515, h577, h587, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h589 | h589
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                                      · rcases h1bigk with h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c | h591c
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h577, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          rcases p591_3 (m.d 0 1) (by simp) with h594 | h594
                                          · rcases p591_3 (m.d 1 2) (by simp) with h595 | h595
                                            · linarith only [h0, h595, hlam]
                                            · linarith only [h577, h595, hlam]
                                          · linarith only [h594, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          rcases p591_3 (m.d 0 1) (by simp) with h599 | h599
                                          · rcases p591_3 (m.d 1 2) (by simp) with h600 | h600
                                            · linarith only [h0, h600, hlam]
                                            · linarith only [h578, h600, hlam]
                                          · linarith only [h599, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          rcases p591_3 (m.d 0 1) (by simp) with h604 | h604
                                          · rcases p591_3 (m.d 1 2) (by simp) with h605 | h605
                                            · linarith only [h0, h605, hlam]
                                            · linarith only [h579, h605, hlam]
                                          · linarith only [h604, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, h577, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, h577, h582, h584, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, h577, h582, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h1, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h577, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h580, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h582, hlam, p591_1]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi1]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h578, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h0, h577, h578, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h577, h580, h582, hc34, hlam, hphi, ht23, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h2, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h579, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h2, h577, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p591_1, u2ehi2]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [h584, hlam, p591_0]
                                        · have p591_0 := h591c.1
                                          have p591_1 := h591c.2.1
                                          have p591_2 := h591c.2.2.1
                                          have p591_3 := h591c.2.2.2
                                          linarith only [hlam, p591_0]
                                      · linarith only [h1, h577, h590, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                    · linarith only [h0, h578, h584, h589, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h576, h578, h584, h6, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h5, h577, h579, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h577, h578, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h577, h6, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                          · linarith only [h1, h6, h638, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h640 | h640
                            · linarith only [h1, h515, h640, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                              · linarith only [h0, h1, h576, h6, h635, h636, h642, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h644 | h644
                                · linarith only [h1, h6, h635, h644, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h646 | h646
                                  · linarith only [h1, h515, h635, h646, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h648 | h648
                                    · linarith only [h1, h576, h6, h635, h648, hc24, hlam, hphi, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h650 | h650
                                      · linarith only [h1, h576, h6, h635, h650, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h1, h6, h635, h650, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h5, h635, h637, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h635, h636, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h3, h6, h635, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h658 | h658
          · linarith only [h3, h658, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h660 | h660
            · linarith only [h3, h660, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h662 | h662
              · rcases m.htr 0 3 5 (by decide) (by decide) with h663 | h663
                · rcases m.htr 0 4 5 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h665 | h665
                    · linarith only [h0, h3, h665, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                      · linarith only [h0, h658, h667, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
                        · linarith only [h0, h660, h669, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h673 | h673
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h674 | h674
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h675 | h675
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h676 | h676
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h677 | h677
                                      · rcases h1bigk with h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c | h678c
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          rcases p678_3 (m.d 0 1) (by simp) with h680 | h680
                                          · rcases p678_3 (m.d 1 2) (by simp) with h681 | h681
                                            · linarith only [h681, hlam, p678_0]
                                            · rcases p678_3 (m.d 1 3) (by simp) with h683 | h683
                                              · linarith only [h1, h683, hlam]
                                              · linarith only [h665, h683, hlam]
                                          · linarith only [h680, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h671, h677, hc01, hc45, hlam, hphi, ht0b, ht5b, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          rcases p678_3 (m.d 0 1) (by simp) with h688 | h688
                                          · rcases p678_3 (m.d 1 2) (by simp) with h689 | h689
                                            · linarith only [h0, h689, hlam]
                                            · rcases p678_3 (m.d 1 3) (by simp) with h691 | h691
                                              · linarith only [h1, h691, hlam]
                                              · linarith only [h671, h691, hlam]
                                          · linarith only [h688, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          rcases p678_3 (m.d 0 1) (by simp) with h695 | h695
                                          · rcases p678_3 (m.d 1 2) (by simp) with h696 | h696
                                            · linarith only [h0, h696, hlam]
                                            · rcases p678_3 (m.d 1 3) (by simp) with h698 | h698
                                              · linarith only [h1, h698, hlam]
                                              · linarith only [h672, h698, hlam]
                                          · linarith only [h695, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h0, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h665, hlam, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h667, hlam, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h669, hlam, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, h667, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, h669, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, h671, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h667, h674, hc23, hlam, hphi, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h671, hlam, p678_1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h1, h669, h671, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h2, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p678_1, u2ehi1]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h672, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [h673, hlam, p678_0]
                                        · have p678_0 := h678c.1
                                          have p678_1 := h678c.2.1
                                          have p678_2 := h678c.2.2.1
                                          have p678_3 := h678c.2.2.2
                                          linarith only [hlam, p678_0]
                                      · rcases h1bigk with h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c | h722c
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          rcases p722_3 (m.d 0 1) (by simp) with h724 | h724
                                          · rcases p722_3 (m.d 1 2) (by simp) with h725 | h725
                                            · linarith only [h725, hlam, p722_0]
                                            · rcases p722_3 (m.d 1 3) (by simp) with h727 | h727
                                              · linarith only [h1, h727, hlam]
                                              · linarith only [h665, h727, hlam]
                                          · linarith only [h724, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h671, h673, h677, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h673, h677, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          rcases p722_3 (m.d 0 1) (by simp) with h733 | h733
                                          · rcases p722_3 (m.d 1 2) (by simp) with h734 | h734
                                            · linarith only [h0, h734, hlam]
                                            · rcases p722_3 (m.d 1 3) (by simp) with h736 | h736
                                              · linarith only [h1, h736, hlam]
                                              · linarith only [h672, h736, hlam]
                                          · linarith only [h733, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h0, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h665, hlam, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h667, hlam, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h669, hlam, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h1, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h1, h673, h677, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h1, h669, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h0, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h667, h674, hc23, hlam, hphi, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h671, hlam, p722_1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h1, h669, h671, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h2, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p722_1, u2ehi1]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h672, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [h673, hlam, p722_0]
                                        · have p722_0 := h722c.1
                                          have p722_1 := h722c.2.1
                                          have p722_2 := h722c.2.2.1
                                          have p722_3 := h722c.2.2.2
                                          linarith only [hlam, p722_0]
                                    · linarith only [h1, h658, h671, h673, h676, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1, h672, h675, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h3, h674, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h3, h662, h664, h667, h673, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h3, h663, h665, h672, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h3, h662, h665, h671, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h766 | h766
                    · linarith only [h0, h658, h766, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h768 | h768
                      · linarith only [h0, h3, h768, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h770 | h770
                        · linarith only [h0, h660, h770, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h772 | h772
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h773 | h773
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h774 | h774
                              · linarith only [h1, h658, h664, h772, h774, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h776 | h776
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h777 | h777
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h778 | h778
                                    · linarith only [h0, h658, h664, h778, hc24, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h658, h778, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                  · linarith only [h0, h3, h777, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h3, h776, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h3, h663, h766, h773, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h3, h662, h766, h772, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h785 | h785
                  · linarith only [h662, h663, h785, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h787 | h787
                    · linarith only [h0, h658, h787, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · linarith only [h0, h658, h789, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h791 | h791
                        · linarith only [h0, h658, h785, h791, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h793 | h793
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h794 | h794
                            · linarith only [h1, h658, h662, h663, h794, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
                              · linarith only [h0, h658, h785, h789, h796, hc24, hlam, hphi, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h799 | h799
                                  · linarith only [h0, h658, h662, h663, h799, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h3, h799, hc35, hlam, hphi, ht23, u2ehi1]
                                · linarith only [h0, h1, h3, h793, h798, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h662, h663, h793, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
                · rcases m.htr 0 4 5 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h806 | h806
                    · linarith only [h0, h658, h806, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h808 | h808
                      · linarith only [h0, h3, h808, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h810 | h810
                        · linarith only [h0, h660, h662, h804, h810, hc34, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h812 | h812
                          · linarith only [h1, h660, h662, h804, h812, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h814 | h814
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h815 | h815
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h816 | h816
                                · linarith only [h0, h660, h662, h804, h816, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h816, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h662, h804, h805, h806, h812, h815, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h662, h804, h806, h814, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h662, h804, h805, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h822 | h822
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h823 | h823
                    · linarith only [h0, h3, h823, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h825 | h825
                      · linarith only [h0, h3, h825, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
                        · linarith only [h0, h660, h827, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
                          · linarith only [h1, h662, h829, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
                            · linarith only [h1, h804, h831, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h833 | h833
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h834 | h834
                                · linarith only [h0, h3, h662, h834, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h834, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h662, h822, h825, h833, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
                    · linarith only [h0, h3, h838, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
                      · linarith only [h0, h3, h840, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h842 | h842
                        · linarith only [h0, h660, h842, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h844 | h844
                          · linarith only [h1, h662, h844, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                            · linarith only [h1, h804, h846, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h848 | h848
                              · linarith only [h3, h662, h822, h840, h848, hc24, hlam, hphi, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h850 | h850
                                · linarith only [h0, h3, h662, h850, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h3, h850, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h853 | h853
        · rcases m.htr 0 2 4 (by decide) (by decide) with h854 | h854
          · rcases m.htr 0 2 5 (by decide) (by decide) with h855 | h855
            · linarith only [h0, h2, h855, hlam]
            · linarith only [h853, h855, hc25, hlam, hphi, u2ehi2]
          · linarith only [h853, h854, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h859 | h859
          · linarith only [h853, h859, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h861 | h861
            · linarith only [h853, h861, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h863 | h863
              · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
                · linarith only [h1, h2, h864, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h866 | h866
                  · linarith only [h0, h2, h863, h864, h866, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h868 | h868
                    · linarith only [h0, h2, h868, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h870 | h870
                      · linarith only [h1, h2, h859, h868, h870, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
                        · linarith only [h0, h853, h872, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h2, h868, h872, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h875 | h875
                · linarith only [h0, h2, h863, h875, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h877 | h877
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h878 | h878
                    · linarith only [h0, h2, h878, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
                      · linarith only [h0, h853, h880, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h882 | h882
                        · linarith only [h1, h2, h878, h882, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h1, h2, h878, h882, hc25, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                    · linarith only [h0, h853, h885, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                      · linarith only [h0, h859, h887, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                        · linarith only [h1, h2, h885, h889, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · linarith only [h1, h2, h885, h889, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h892 | h892
      · rcases m.htr 0 2 3 (by decide) (by decide) with h893 | h893
        · linarith only [h0, h1, h893, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h895 | h895
          · linarith only [h893, h895, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h897 | h897
            · linarith only [h893, h897, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h899 | h899
              · rcases m.htr 0 3 5 (by decide) (by decide) with h900 | h900
                · rcases m.htr 0 4 5 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                    · linarith only [h0, h1, h893, h902, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h902, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                    · linarith only [h0, h1, h905, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h905, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h900, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h899, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h910 | h910
        · linarith only [h0, h1, h910, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h912 | h912
          · linarith only [h910, h912, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h914 | h914
            · linarith only [h910, h914, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h916 | h916
              · rcases m.htr 0 3 5 (by decide) (by decide) with h917 | h917
                · rcases m.htr 0 4 5 (by decide) (by decide) with h918 | h918
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                    · linarith only [h0, h1, h910, h919, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h919, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
                    · linarith only [h0, h1, h922, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h922, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h917, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h916, hc34, hlam, hphi, ht23, u2ehi1]
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0 m hb1 hb2 hb4 hb5 h0

end R2N4
