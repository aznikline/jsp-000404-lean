import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S7
import Jsp000404.R1LeavesN7_14S16
import Jsp000404.R1LeavesN7_14S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6144 | h6144
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6145 | h6145
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6146 | h6146
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6147 | h6147
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6148 | h6148
          · linarith only [h4610, h4611, h6148, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6150 | h6150
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6151 | h6151
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6152 | h6152
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6153 | h6153
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6154 | h6154
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6155 | h6155
                      · linarith only [h4610, h6148, h6155, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6157 | h6157
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6158 | h6158
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6159 | h6159
                            · linarith only [h4610, h4611, h6152, h6155, h6159, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6161 | h6161
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6162 | h6162
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6163 | h6163
                                  · rcases h0bigk with h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c | h6164c
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h0, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4611, h6155, hc03, hc34, hlam, hphi, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4611, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      rcases p6164_3 (m.d 0 1) (by simp) with h6169 | h6169
                                      · rcases p6164_3 (m.d 0 2) (by simp) with h6170 | h6170
                                        · rcases p6164_3 (m.d 0 3) (by simp) with h6171 | h6171
                                          · linarith only [h4610, h6171, hlam]
                                          · linarith only [h6150, h6171, hlam]
                                        · linarith only [h6147, h6170, hlam]
                                      · linarith only [h6144, h6169, hlam]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4610, h6152, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6164_1, u0elo1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4610, h6152, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6164_1, u0elo1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4610, h4611, h6152, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6164_1, u0elo1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      rcases p6164_3 (m.d 0 1) (by simp) with h6180 | h6180
                                      · linarith only [h0, h6180, hlam]
                                      · linarith only [h6144, h6180, hlam]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4610, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6145, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6148, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      rcases p6164_3 (m.d 0 1) (by simp) with h6187 | h6187
                                      · rcases p6164_3 (m.d 0 2) (by simp) with h6188 | h6188
                                        · rcases p6164_3 (m.d 0 3) (by simp) with h6189 | h6189
                                          · rcases p6164_3 (m.d 0 4) (by simp) with h6190 | h6190
                                            · rcases p6164_3 (m.d 0 5) (by simp) with h6191 | h6191
                                              · linarith only [h6150, h6191, hlam]
                                              · rcases h2bigk with h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h0, hlam, p6193_1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6193_1, u0elo1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6159, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6193_1, u0elo1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  rcases p6193_3 (m.d 0 2) (by simp) with h6198 | h6198
                                                  · rcases p6193_3 (m.d 1 2) (by simp) with h6199 | h6199
                                                    · rcases p6193_3 (m.d 2 3) (by simp) with h6200 | h6200
                                                      · linarith only [h6145, h6200, hlam]
                                                      · linarith only [h6161, h6200, hlam]
                                                    · linarith only [h6154, h6199, hlam]
                                                  · linarith only [h6198, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h0, h4610, h6144, h6154, h6161, h6163, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6164_1, p6193_1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  rcases p6193_3 (m.d 0 2) (by simp) with h6207 | h6207
                                                  · linarith only [h0, h6207, hlam]
                                                  · linarith only [h6145, h6207, hlam]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  rcases p6193_3 (m.d 0 2) (by simp) with h6210 | h6210
                                                  · linarith only [h0, h6210, hlam]
                                                  · linarith only [h6146, h6210, hlam]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h0, h4610, h6144, h6154, hlam, p6164_1, p6193_2]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6145, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6152, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6159, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h4610, h6152, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6193_1, u0elo0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6146, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6153, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6146, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6193_1, u0elo1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6146, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6193_1, u0elo1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6147, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6154, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6161, hlam, p6193_1]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [h6162, hlam, p6193_0]
                                                · have p6193_0 := h6193c.1
                                                  have p6193_1 := h6193c.2.1
                                                  have p6193_2 := h6193c.2.2.1
                                                  have p6193_3 := h6193c.2.2.2
                                                  linarith only [hlam, p6193_0]
                                            · linarith only [h6151, h6190, hlam]
                                          · linarith only [h6150, h6189, hlam]
                                        · linarith only [h6147, h6188, hlam]
                                      · linarith only [h6144, h6187, hlam]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h4610, h6146, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6164_1, u0elo1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6146, hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6145, h6161, h6163, hc45, hlam, hphi, ht0b, ht5b, p6164_1, u0elo3]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      rcases p6164_3 (m.d 0 1) (by simp) with h6237 | h6237
                                      · linarith only [h4611, h6237, hlam]
                                      · linarith only [h6144, h6237, hlam]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6144, hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6147, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6150, hlam, p6164_0]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [h6151, hlam, p6164_1]
                                    · have p6164_0 := h6164c.1
                                      have p6164_1 := h6164c.2.1
                                      have p6164_2 := h6164c.2.2.1
                                      have p6164_3 := h6164c.2.2.2
                                      linarith only [hlam, p6164_0]
                                  · linarith only [h4610, h4611, h6155, h6163, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h4610, h4611, h6155, h6157, h6158, h6159, h6161, h6162, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h4610, h4611, h6150, h6155, h6161, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6158, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h4610, h4611, h6150, h6155, h6157, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6147, h6154, hlam]
                  · linarith only [h0, h6146, h6153, hlam]
                · linarith only [h0, h6145, h6152, hlam]
              · linarith only [h4611, h6144, h6151, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6254 | h6254
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6255 | h6255
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6256 | h6256
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6257 | h6257
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6258 | h6258
                      · linarith only [h4610, h6148, h6258, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6260 | h6260
                        · linarith only [h4610, h6150, h6260, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6262 | h6262
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6263 | h6263
                            · linarith only [h4611, h6145, h6258, h6263, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6265 | h6265
                              · linarith only [h4610, h6150, h6255, h6265, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6267 | h6267
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6268 | h6268
                                  · rcases h0bigk with h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c | h6269c
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h0, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4610, h4611, h6255, h6258, hc23, hc34, hlam, hphi, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4611, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4610, h4611, h6150, h6255, h6258, hc23, hc34, hlam, hphi, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4610, h6255, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6269_1, u0elo1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      rcases p6269_3 (m.d 0 1) (by simp) with h6277 | h6277
                                      · linarith only [h0, h6277, hlam]
                                      · linarith only [h4610, h6277, hlam]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4611, h6144, h6255, h6260, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6269_1, u0elo1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      rcases p6269_3 (m.d 0 1) (by simp) with h6281 | h6281
                                      · linarith only [h0, h6281, hlam]
                                      · linarith only [h6144, h6281, hlam]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4610, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6145, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6148, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6150, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6144, h6255, h6260, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6269_1, u0elo3]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6146, hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      rcases p6269_3 (m.d 0 1) (by simp) with h6291 | h6291
                                      · linarith only [h4611, h6291, hlam]
                                      · linarith only [h4610, h6291, hlam]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      rcases p6269_3 (m.d 0 1) (by simp) with h6295 | h6295
                                      · linarith only [h4611, h6295, hlam]
                                      · linarith only [h6144, h6295, hlam]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6144, hlam, p6269_0]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6147, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h4610, h4611, h6144, h6255, h6258, hc23, hc34, hlam, hphi, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [h6254, hlam, p6269_1]
                                    · have p6269_0 := h6269c.1
                                      have p6269_1 := h6269c.2.1
                                      have p6269_2 := h6269c.2.2.1
                                      have p6269_3 := h6269c.2.2.2
                                      linarith only [hlam, p6269_0]
                                  · linarith only [h4610, h4611, h6255, h6258, h6268, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h4611, h6144, h6258, h6262, h6263, h6267, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6255, h6262, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6147, h6257, hlam]
                  · linarith only [h0, h6146, h6256, hlam]
                · linarith only [h0, h6145, h6255, hlam]
              · linarith only [h4611, h6144, h6254, hlam]
        · linarith only [h4611, h6144, h6146, h6147, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6311 | h6311
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6312 | h6312
          · linarith only [h0, h4610, h6146, h6312, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6314 | h6314
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6315 | h6315
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6316 | h6316
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6317 | h6317
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6318 | h6318
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6319 | h6319
                      · linarith only [h0, h4610, h6312, h6319, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6321 | h6321
                        · linarith only [h0, h4610, h6146, h6317, h6321, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h4610, h6146, h6314, h6317, h6321, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6146, h6317, h6318, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6325 | h6325
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6326 | h6326
                      · linarith only [h0, h4610, h6312, h6317, h6326, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6328 | h6328
                        · linarith only [h0, h4610, h6317, h6328, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h4610, h6314, h6316, h6317, h6328, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6311, h6325, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h6145, h6316, hlam]
              · linarith only [h0, h4610, h6146, h6314, h6315, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6334 | h6334
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6335 | h6335
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6336 | h6336
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6337 | h6337
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6338 | h6338
                      · linarith only [h0, h4610, h6146, h6336, h6338, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6340 | h6340
                        · linarith only [h0, h4610, h6146, h6314, h6336, h6340, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6342 | h6342
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6343 | h6343
                            · linarith only [h0, h4610, h6146, h6335, h6336, h6338, h6343, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6345 | h6345
                              · linarith only [h4610, h6314, h6335, h6345, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6347 | h6347
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6348 | h6348
                                  · rcases h0bigk with h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c | h6349c
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [hlam, p6349_0]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h0, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h0, h4610, h6146, h6335, h6336, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h4611, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h0, h6146, h6336, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6146, h6336, hc01, hc12, hlam, hphi, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [hlam, p6349_0]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h4610, h6146, h6335, h6336, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6146, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6144, h6146, h6336, h6337, h6347, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h4610, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6145, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [hlam, p6349_0]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6312, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6314, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h4610, h6335, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6349_1, u0elo3]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h0, h4610, h6146, h6335, h6336, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      rcases p6349_3 (m.d 0 1) (by simp) with h6367 | h6367
                                      · linarith only [h4611, h6367, hlam]
                                      · linarith only [h4610, h6367, hlam]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [hlam, p6349_0]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      rcases p6349_3 (m.d 0 1) (by simp) with h6371 | h6371
                                      · linarith only [h4611, h6371, hlam]
                                      · linarith only [h6144, h6371, hlam]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6144, hlam, p6349_0]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6311, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h4610, h4611, h6144, h6335, h6338, hc23, hc34, hlam, hphi, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [h6334, hlam, p6349_1]
                                    · have p6349_0 := h6349c.1
                                      have p6349_1 := h6349c.2.1
                                      have p6349_2 := h6349c.2.2.1
                                      have p6349_3 := h6349c.2.2.2
                                      linarith only [hlam, p6349_0]
                                  · linarith only [h4610, h4611, h6335, h6338, h6348, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h6144, h6146, h6342, h6347, hlam]
                          · linarith only [h0, h6144, h6146, h6335, h6336, h6340, h6342, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6311, h6337, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6383 | h6383
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6384 | h6384
                      · linarith only [h4610, h6312, h6384, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6386 | h6386
                        · linarith only [h0, h4610, h6314, h6334, h6336, h6386, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6388 | h6388
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6389 | h6389
                            · linarith only [h0, h4611, h6145, h6336, h6384, h6389, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h6144, h6335, h6336, h6386, h6389, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6144, h6335, h6336, h6386, h6388, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6311, h6383, hlam]
                · linarith only [h0, h6145, h6335, hlam]
              · linarith only [h0, h6144, h6146, h6334, hlam]
        · linarith only [h0, h6144, h6311, hlam]
    · linarith only [h0, h4610, h6145, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6398 | h6398
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6399 | h6399
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6400 | h6400
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6401 | h6401
          · linarith only [h4610, h4611, h6401, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6403 | h6403
            · linarith only [h4610, h6144, h6403, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6405 | h6405
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6406 | h6406
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6407 | h6407
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6408 | h6408
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6409 | h6409
                      · linarith only [h4610, h6401, h6409, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6411 | h6411
                        · linarith only [h4610, h6144, h6403, h6411, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6413 | h6413
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6414 | h6414
                            · linarith only [h4610, h6144, h6398, h6409, h6413, h6414, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6416 | h6416
                              · linarith only [h4610, h6144, h6406, h6411, h6416, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6418 | h6418
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6419 | h6419
                                  · rcases h0bigk with h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c | h6420c
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [hlam, p6420_0]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h0, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6144, h6409, h6413, hc03, hc34, hlam, hphi, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4611, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6144, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [hlam, p6420_0]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      rcases p6420_3 (m.d 0 1) (by simp) with h6428 | h6428
                                      · linarith only [h0, h6428, hlam]
                                      · linarith only [h4610, h6428, hlam]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, h6144, h6405, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, h6144, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6398, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [hlam, p6420_0]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6401, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6403, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo3]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6399, hlam, p6420_0]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      rcases p6420_3 (m.d 0 1) (by simp) with h6440 | h6440
                                      · linarith only [h4611, h6440, hlam]
                                      · linarith only [h4610, h6440, hlam]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [hlam, p6420_0]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, h6144, h6399, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h4610, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6420_1, u0elo4]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6400, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      rcases p6420_3 (m.d 0 1) (by simp) with h6447 | h6447
                                      · linarith only [h6144, h6447, hlam]
                                      · linarith only [h4610, h6447, hlam]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [h6405, hlam, p6420_1]
                                    · have p6420_0 := h6420c.1
                                      have p6420_1 := h6420c.2.1
                                      have p6420_2 := h6420c.2.2.1
                                      have p6420_3 := h6420c.2.2.2
                                      linarith only [hlam, p6420_0]
                                  · linarith only [h4611, h6399, h6409, h6418, h6419, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6453 | h6453
                                  · rcases h0bigk with h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c | h6454c
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [hlam, p6454_0]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h0, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6144, h6406, h6411, hc23, hc35, hlam, hphi, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4611, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6144, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6454_1, u0elo1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [hlam, p6454_0]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      rcases p6454_3 (m.d 0 1) (by simp) with h6462 | h6462
                                      · linarith only [h0, h6462, hlam]
                                      · linarith only [h4610, h6462, hlam]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6405, h6418, hc24, hlam, hphi, ht0b, ht45, ht5b, p6454_1, u0elo1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6144, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6454_1, u0elo1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6398, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [hlam, p6454_0]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6401, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6403, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6454_1, u0elo3]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6399, hlam, p6454_0]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      rcases p6454_3 (m.d 0 1) (by simp) with h6474 | h6474
                                      · linarith only [h4611, h6474, hlam]
                                      · linarith only [h4610, h6474, hlam]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [hlam, p6454_0]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6144, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6454_1, u0elo3]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h4610, h6406, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6454_1, u0elo4]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6400, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      rcases p6454_3 (m.d 0 1) (by simp) with h6481 | h6481
                                      · linarith only [h6144, h6481, hlam]
                                      · linarith only [h4610, h6481, hlam]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [h6405, hlam, p6454_1]
                                    · have p6454_0 := h6454c.1
                                      have p6454_1 := h6454c.2.1
                                      have p6454_2 := h6454c.2.2.1
                                      have p6454_3 := h6454c.2.2.2
                                      linarith only [hlam, p6454_0]
                                  · linarith only [h4610, h4611, h6406, h6409, h6453, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h4611, h6405, h6413, hlam]
                    · linarith only [h0, h6400, h6408, hlam]
                  · linarith only [h0, h6399, h6407, hlam]
                · linarith only [h0, h6398, h6406, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6491 | h6491
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6492 | h6492
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6493 | h6493
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6494 | h6494
                      · linarith only [h4610, h4611, h6405, h6494, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6496 | h6496
                        · linarith only [h4610, h6403, h6496, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6498 | h6498
                          · linarith only [h4610, h4611, h6405, h6494, h6498, hc13, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6491, h6498, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h4610, h6400, h6491, h6493, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4610, h6399, h6492, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h4610, h6398, h6491, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6504 | h6504
          · linarith only [h4610, h4611, h6504, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6506 | h6506
            · linarith only [h0, h4610, h6400, h6506, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6508 | h6508
              · linarith only [h6399, h6400, h6508, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6510 | h6510
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6511 | h6511
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6512 | h6512
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6513 | h6513
                      · linarith only [h4610, h6504, h6513, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6515 | h6515
                        · linarith only [h4610, h4611, h6399, h6400, h6506, h6515, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6517 | h6517
                          · linarith only [h4610, h4611, h6508, h6513, h6517, hc13, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6510, h6517, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6520 | h6520
                      · linarith only [h0, h4610, h6512, h6520, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6522 | h6522
                        · linarith only [h4610, h4611, h6511, h6512, h6522, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6524 | h6524
                          · linarith only [h4610, h4611, h6508, h6510, h6511, h6512, h6524, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h4610, h4611, h6510, h6524, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h4610, h6399, h6510, h6511, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h6398, h6510, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6529 | h6529
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6530 | h6530
          · linarith only [h0, h4610, h6399, h6530, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6532 | h6532
            · linarith only [h4610, h6144, h6532, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6534 | h6534
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6535 | h6535
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6536 | h6536
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6537 | h6537
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6538 | h6538
                      · linarith only [h4610, h6144, h6399, h6529, h6530, h6536, h6538, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6540 | h6540
                        · linarith only [h4610, h6144, h6532, h6540, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6542 | h6542
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6543 | h6543
                            · linarith only [h6398, h6399, h6536, h6538, h6543, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6545 | h6545
                              · linarith only [h4610, h6144, h6535, h6540, h6545, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6547 | h6547
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6548 | h6548
                                  · rcases h0bigk with h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [hlam, p6549_0]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h0, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6144, h6399, h6529, h6536, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4611, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6144, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6399, h6536, hc01, hc12, hlam, hphi, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [hlam, p6549_0]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, h6399, h6535, h6536, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6399, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6399, h6536, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6398, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [hlam, p6549_0]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6530, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6532, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, h6535, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6549_1, u0elo3]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6399, h6529, h6536, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      rcases p6549_3 (m.d 0 1) (by simp) with h6567 | h6567
                                      · linarith only [h4611, h6567, hlam]
                                      · linarith only [h4610, h6567, hlam]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [hlam, p6549_0]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, h6144, h6399, h6535, h6536, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, h6529, h6535, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6549_1, u0elo1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6529, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h4610, h6399, h6529, h6535, h6536, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [h6534, hlam, p6549_1]
                                    · have p6549_0 := h6549c.1
                                      have p6549_1 := h6549c.2.1
                                      have p6549_2 := h6549c.2.2.1
                                      have p6549_3 := h6549c.2.2.2
                                      linarith only [hlam, p6549_0]
                                  · linarith only [h0, h4610, h6399, h6535, h6536, h6538, h6548, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h6399, h6529, h6534, h6547, hlam]
                          · linarith only [h6399, h6529, h6534, h6536, h6542, hlam]
                    · linarith only [h6399, h6529, h6537, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6581 | h6581
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6582 | h6582
                      · linarith only [h4610, h6144, h6536, h6581, h6582, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6584 | h6584
                        · linarith only [h4610, h6144, h6536, h6581, h6584, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6586 | h6586
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6587 | h6587
                            · linarith only [h4610, h4611, h6144, h6535, h6536, h6581, h6582, h6587, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h4610, h6144, h6535, h6536, h6581, h6587, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6535, h6586, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h4610, h6399, h6529, h6535, h6581, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h6398, h6535, hlam]
              · linarith only [h6399, h6529, h6534, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6594 | h6594
          · linarith only [h0, h4610, h6399, h6594, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6596 | h6596
            · linarith only [h0, h4610, h6529, h6596, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6598 | h6598
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6599 | h6599
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6600 | h6600
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6601 | h6601
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6602 | h6602
                      · linarith only [h4610, h6594, h6602, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6604 | h6604
                        · linarith only [h0, h4610, h6399, h6596, h6600, h6604, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6606 | h6606
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6607 | h6607
                            · linarith only [h4611, h6398, h6399, h6600, h6602, h6607, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6609 | h6609
                              · linarith only [h4610, h6529, h6599, h6601, h6604, h6609, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6611 | h6611
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6612 | h6612
                                  · rcases h0bigk with h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c | h6613c
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [hlam, p6613_0]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h0, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h0, h4610, h6529, h6599, h6601, h6602, h6606, hc23, hc34, hlam, hphi, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h4611, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6144, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6529, h6601, h6606, hc01, hc14, hlam, hphi, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [hlam, p6613_0]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h4610, h6529, h6599, h6601, h6602, h6606, hc23, hc34, hlam, hphi, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6399, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6529, hlam, p6613_0]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h4610, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6398, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [hlam, p6613_0]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6594, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6596, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h4610, h6599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6613_1, u0elo3]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h0, h4610, h6599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6613_1, u0elo3]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      rcases p6613_3 (m.d 0 1) (by simp) with h6631 | h6631
                                      · linarith only [h4611, h6631, hlam]
                                      · linarith only [h4610, h6631, hlam]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [hlam, p6613_0]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h0, h4610, h6399, h6529, h6599, h6600, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h4610, h6599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6613_1, u0elo4]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h0, h4610, h6529, h6599, h6600, h6611, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      rcases p6613_3 (m.d 0 1) (by simp) with h6638 | h6638
                                      · linarith only [h6144, h6638, hlam]
                                      · linarith only [h4610, h6638, hlam]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [h6598, hlam, p6613_1]
                                    · have p6613_0 := h6613c.1
                                      have p6613_1 := h6613c.2.1
                                      have p6613_2 := h6613c.2.2.1
                                      have p6613_3 := h6613c.2.2.2
                                      linarith only [hlam, p6613_0]
                                  · linarith only [h4610, h4611, h6599, h6602, h6612, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h6399, h6598, h6611, hlam]
                          · linarith only [h4610, h4611, h6399, h6598, h6599, h6600, h6606, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h4610, h6399, h6599, h6600, h6601, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6647 | h6647
                    · linarith only [h0, h4610, h6529, h6599, h6600, h6647, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6649 | h6649
                      · linarith only [h0, h4610, h6600, h6649, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6651 | h6651
                        · linarith only [h0, h4610, h6600, h6651, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6653 | h6653
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6654 | h6654
                            · linarith only [h0, h4610, h6599, h6600, h6649, h6654, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h4610, h6600, h6654, hc13, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6598, h6599, h6653, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h4610, h6398, h6599, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6659 | h6659
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6660 | h6660
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6661 | h6661
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6662 | h6662
                      · linarith only [h4610, h4611, h6598, h6662, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6664 | h6664
                        · linarith only [h0, h4610, h6529, h6596, h6661, h6664, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6666 | h6666
                          · linarith only [h0, h4610, h6399, h6598, h6659, h6662, h6666, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6659, h6666, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h4610, h6399, h6659, h6660, h6661, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6670 | h6670
                    · linarith only [h0, h4610, h6529, h6659, h6660, h6670, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6672 | h6672
                      · linarith only [h0, h4610, h6660, h6672, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6674 | h6674
                        · linarith only [h0, h4610, h6660, h6674, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6676 | h6676
                          · linarith only [h0, h4610, h6399, h6598, h6659, h6672, h6676, hc23, hc34, hlam, hphi]
                          · linarith only [h4610, h4611, h6659, h6676, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h4610, h6398, h6659, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
    · linarith only [h0, h4610, h6398, hlam]

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h4611 | h4611
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0 m hb0 hb2 hb3 hb5 hg0 h4610 h4611
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x1 m hb0 hb2 hb3 hb5 hg0 h4610 h4611

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s5 m hb0 hb2 hb3 hb5 h0 h4610

set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h4610 | h4610
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0 m hb0 hb2 hb3 hb5 hg0 h4610
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x1 m hb0 hb2 hb3 hb5 hg0 h4610

set_option maxHeartbeats 23974000 in
set_option maxHeartbeats 23974000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4 m hb0 hb2 hb3 hb5 h0

end R2N4
