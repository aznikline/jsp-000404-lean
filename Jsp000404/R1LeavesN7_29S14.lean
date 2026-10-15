import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3964 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4232 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4233 | h4233
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4234 | h4234
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4235 | h4235
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4236 | h4236
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4237 | h4237
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4238 | h4238
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4239 | h4239
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4240 | h4240
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4241 | h4241
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4242 | h4242
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4243 | h4243
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4244 | h4244
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4245 | h4245
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4246 | h4246
                            · linarith only [h0, h4232, h4243, h4246, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h4232, h4243, h4245, h4246, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4249 | h4249
                            · linarith only [h0, h4232, h4243, h4245, h4249, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · rcases h1bigk with h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c | h4251c
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h0, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3078, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3604, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3964, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hc01, hlam, hphi, p4251_1, u1elo2]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4237, hlam, p4251_1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3604, h4236, h4237, h4245, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3964, h4237, hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hc01, hlam, hphi, p4251_1, u1elo3]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4238, hlam, p4251_1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4240, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h3964, h4237, h4240, hc01, hlam, hphi, p4251_1, u1elo1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hc01, hlam, hphi, p4251_1, u1elo4]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4239, hlam, p4251_1]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4241, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [h4242, hlam, p4251_0]
                              · have p4251_0 := h4251c.1
                                have p4251_1 := h4251c.2.1
                                have p4251_2 := h4251c.2.2.1
                                have p4251_3 := h4251c.2.2.2
                                linarith only [hlam, p4251_0]
                        · linarith only [h0, h4232, h4235, h4243, h4244, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4278 | h4278
                        · linarith only [h0, h4232, h4234, h4243, h4278, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4280 | h4280
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4281 | h4281
                            · rcases h1bigk with h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h0, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3078, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3604, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, h4242, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hc01, hlam, hphi, p4282_1, u1elo2]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4237, hlam, p4282_1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, h4237, h4242, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, h4237, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hc01, hlam, hphi, p4282_1, u1elo3]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4238, hlam, p4282_1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4240, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h3964, h4237, h4240, hc01, hlam, hphi, p4282_1, u1elo1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hc01, hlam, hphi, p4282_1, u1elo4]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4239, hlam, p4282_1]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4241, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [h4242, hlam, p4282_0]
                              · have p4282_0 := h4282c.1
                                have p4282_1 := h4282c.2.1
                                have p4282_2 := h4282c.2.2.1
                                have p4282_3 := h4282c.2.2.2
                                linarith only [hlam, p4282_0]
                            · linarith only [h4238, h4280, h4281, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4309 | h4309
                            · linarith only [h3078, h4234, h4237, h4243, h4280, h4309, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · linarith only [h3078, h4234, h4236, h4237, h4243, h4309, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h3078, h3604, h4234, h4236, h4237, h4242, hc01, hlam, hphi, u1elo1]
                  · linarith only [h3078, h4235, h4241, hlam]
                · linarith only [h3078, h4234, h4240, hlam]
              · linarith only [h0, h4233, h4239, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4316 | h4316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4317 | h4317
                · linarith only [h4237, h4238, h4317, hlam]
                · linarith only [h3078, h3604, h4234, h4317, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h3078, h4233, h4234, h4236, h4316, hc01, hlam, hphi, u1elo2]
          · linarith only [h0, h4232, h4237, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4322 | h4322
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4323 | h4323
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4324 | h4324
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4325 | h4325
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4326 | h4326
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4327 | h4327
                    · linarith only [h3604, h4236, h4322, h4325, h4327, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4329 | h4329
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4330 | h4330
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4331 | h4331
                          · linarith only [h0, h3604, h4232, h4236, h4329, h4331, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4333 | h4333
                            · linarith only [h0, h4232, h4327, h4329, h4333, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases h1bigk with h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c | h4335c
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h0, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3078, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3604, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3964, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hc01, hlam, hphi, p4335_1, u1elo2]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4322, hlam, p4335_1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3604, h4322, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3964, h4322, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hc01, hlam, hphi, p4335_1, u1elo3]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4323, hlam, p4335_1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4325, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4327, hlam, p4335_1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hc01, hlam, hphi, p4335_1, u1elo4]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4324, hlam, p4335_1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h4326, hlam, p4335_0]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [h3604, h4322, h4326, hc01, hlam, hphi, p4335_1, u1elo1]
                              · have p4335_0 := h4335c.1
                                have p4335_1 := h4335c.2.1
                                have p4335_2 := h4335c.2.2.1
                                have p4335_3 := h4335c.2.2.2
                                linarith only [hlam, p4335_0]
                        · linarith only [h0, h4232, h4235, h4329, h4330, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4362 | h4362
                        · linarith only [h0, h4232, h4234, h4329, h4362, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4364 | h4364
                          · linarith only [h3604, h4327, h4364, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4366 | h4366
                            · linarith only [h0, h3604, h4232, h4234, h4327, h4366, hc01, hlam, hphi, u1elo1]
                            · rcases h1bigk with h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h0, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3078, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3604, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3964, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hc01, hlam, hphi, p4368_1, u1elo2]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4322, hlam, p4368_1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3604, h4322, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3964, h4322, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hc01, hlam, hphi, p4368_1, u1elo3]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4323, hlam, p4368_1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4325, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4327, hlam, p4368_1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hc01, hlam, hphi, p4368_1, u1elo4]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4324, hlam, p4368_1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h4326, hlam, p4368_0]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [h3604, h4322, h4326, hc01, hlam, hphi, p4368_1, u1elo1]
                              · have p4368_0 := h4368c.1
                                have p4368_1 := h4368c.2.1
                                have p4368_2 := h4368c.2.2.1
                                have p4368_3 := h4368c.2.2.2
                                linarith only [hlam, p4368_0]
                  · linarith only [h0, h3078, h4232, h4235, h4326, hc01, hlam, hphi, u1elo1]
                · linarith only [h3078, h3604, h4234, h4325, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h4233, h4324, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4397 | h4397
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4398 | h4398
                · linarith only [h4322, h4323, h4398, hlam]
                · linarith only [h0, h3078, h4232, h4234, h4398, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h4233, h4397, hlam]
          · linarith only [h0, h4232, h4322, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4403 | h4403
        · linarith only [h4234, h4235, h4403, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4405 | h4405
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4406 | h4406
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4407 | h4407
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4408 | h4408
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4409 | h4409
                  · linarith only [h4234, h4235, h4405, h4409, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4411 | h4411
                    · linarith only [h3604, h4403, h4408, h4409, h4411, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4413 | h4413
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4414 | h4414
                        · linarith only [h3078, h4409, h4414, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4416 | h4416
                          · linarith only [h3078, h3604, h4232, h4403, h4413, h4416, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4418 | h4418
                            · linarith only [h0, h3604, h4233, h4411, h4413, h4414, h4418, hc01, hlam, hphi, u1elo1]
                            · rcases h1bigk with h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c | h4420c
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h0, hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3078, hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3604, hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3964, hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hc01, hlam, hphi, p4420_1, u1elo2]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4405, hlam, p4420_1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3604, h4405, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4409, hlam, p4420_1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hc01, hlam, hphi, p4420_1, u1elo3]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4406, hlam, p4420_1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4408, hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hlam, p4420_0]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4411, hlam, p4420_1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4407, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h4407, hlam, p4420_1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3078, h4407, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [h3604, h4407, hc01, hlam, hphi, p4420_1, u1elo1]
                              · have p4420_0 := h4420c.1
                                have p4420_1 := h4420c.2.1
                                have p4420_2 := h4420c.2.2.1
                                have p4420_3 := h4420c.2.2.2
                                linarith only [hlam, p4420_0]
                      · linarith only [h4234, h4235, h4413, hc23, hc35, hlam, hphi]
                · linarith only [h3078, h4234, h4408, hlam]
              · linarith only [h0, h4233, h4407, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4449 | h4449
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4450 | h4450
                · linarith only [h4405, h4406, h4450, hlam]
                · linarith only [h4234, h4235, h4450, hc13, hc35, hlam, hphi]
              · linarith only [h0, h4233, h4449, hlam]
          · linarith only [h0, h4232, h4405, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4455 | h4455
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4456 | h4456
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4457 | h4457
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4458 | h4458
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4459 | h4459
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4460 | h4460
                · linarith only [h4234, h4455, h4457, h4460, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4462 | h4462
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4463 | h4463
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4464 | h4464
                      · linarith only [h0, h4232, h4460, h4464, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4466 | h4466
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4467 | h4467
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4468 | h4468
                            · rcases h1bigk with h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c | h4469c
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h0, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3078, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3604, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3964, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3964, h4462, hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hc01, hlam, hphi, p4469_1, u1elo2]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4457, hlam, p4469_1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4460, hlam, p4469_1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3964, h4460, hc01, hc34, hlam, hphi, ht12, ht23, p4469_1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hc01, hlam, hphi, p4469_1, u1elo3]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4458, hlam, p4469_1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3078, h4458, hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h3964, h4458, hc01, hlam, hphi, p4469_1, u1elo1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4462, hc01, hlam, hphi, p4469_1, u1elo2]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4459, hlam, p4469_1]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4462, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [h4463, hlam, p4469_0]
                              · have p4469_0 := h4469c.1
                                have p4469_1 := h4469c.2.1
                                have p4469_2 := h4469c.2.2.1
                                have p4469_3 := h4469c.2.2.2
                                linarith only [hlam, p4469_0]
                            · linarith only [h3078, h4460, h4468, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h3604, h4456, h4458, h4464, h4466, h4467, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h3078, h4455, h4460, h4466, hc23, hc34, hlam, hphi]
                    · linarith only [h3604, h4456, h4463, hlam]
                  · linarith only [h3078, h4455, h4462, hlam]
              · linarith only [h0, h4233, h4459, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4501 | h4501
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4502 | h4502
                · linarith only [h4234, h4455, h4502, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4504 | h4504
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4505 | h4505
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4506 | h4506
                      · linarith only [h3078, h4502, h4506, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4508 | h4508
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4509 | h4509
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4510 | h4510
                            · rcases h1bigk with h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h0, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3078, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3604, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3964, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4458, h4506, hc01, hc34, hlam, hphi, ht12, ht23, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3964, h4458, h4504, h4506, hc01, hc34, hlam, hphi, ht12, ht23, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4458, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3964, h4458, h4506, hc01, hc34, hlam, hphi, ht12, ht23, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hc01, hlam, hphi, p4511_1, u1elo2]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4457, hlam, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4502, hlam, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3964, h4457, h4458, h4506, hc01, hc34, hlam, hphi, ht12, ht23, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hc01, hlam, hphi, p4511_1, u1elo3]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p4511_1, u1elo3]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4511_1, u1elo3]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4511_1, u1elo3]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4504, hc01, hlam, hphi, p4511_1, u1elo2]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4501, hlam, p4511_1]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4504, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [h4505, hlam, p4511_0]
                              · have p4511_0 := h4511c.1
                                have p4511_1 := h4511c.2.1
                                have p4511_2 := h4511c.2.2.1
                                have p4511_3 := h4511c.2.2.2
                                linarith only [hlam, p4511_0]
                            · linarith only [h0, h4458, h4506, h4510, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h3604, h4232, h4456, h4458, h4508, h4509, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                        · linarith only [h3078, h4455, h4457, h4458, h4506, h4508, hc23, hc34, hlam, hphi]
                    · linarith only [h3604, h4456, h4505, hlam]
                  · linarith only [h3078, h4455, h4504, hlam]
              · linarith only [h0, h4233, h4501, hlam]
          · linarith only [h0, h4232, h4457, hlam]
        · linarith only [h4234, h4455, h4456, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4545 | h4545
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4546 | h4546
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4547 | h4547
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4548 | h4548
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4549 | h4549
                · linarith only [h3078, h4234, h4549, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4551 | h4551
                  · linarith only [h3078, h4455, h4547, h4549, h4551, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4553 | h4553
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4554 | h4554
                      · linarith only [h3078, h4549, h4554, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4556 | h4556
                        · linarith only [h3078, h4232, h4551, h4556, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4558 | h4558
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4559 | h4559
                            · rcases h1bigk with h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c | h4560c
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h0, hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3078, hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3604, hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3964, hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hc01, hlam, hphi, p4560_1, u1elo2]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4546, hlam, p4560_1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4549, hlam, p4560_1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4551, hlam, p4560_1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hc01, hlam, hphi, p4560_1, u1elo3]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4547, hlam, p4560_1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3078, h4547, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3964, h4547, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hc01, hlam, hphi, p4560_1, u1elo4]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4548, hlam, p4560_1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h3078, h4548, hc01, hlam, hphi, p4560_1, u1elo1]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [h4553, hlam, p4560_0]
                              · have p4560_0 := h4560c.1
                                have p4560_1 := h4560c.2.1
                                have p4560_2 := h4560c.2.2.1
                                have p4560_3 := h4560c.2.2.2
                                linarith only [hlam, p4560_0]
                            · linarith only [h4234, h4545, h4559, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4587 | h4587
                            · rcases h1bigk with h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c | h4588c
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h0, hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3078, hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3604, hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3964, hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3604, h4545, h4554, h4558, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hc01, hlam, hphi, p4588_1, u1elo2]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4546, hlam, p4588_1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4549, hlam, p4588_1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4551, hlam, p4588_1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hc01, hlam, hphi, p4588_1, u1elo3]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4547, hlam, p4588_1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3078, h4547, hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3964, h4547, hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hc01, hlam, hphi, p4588_1, u1elo4]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4548, hlam, p4588_1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h3078, h4548, hc01, hlam, hphi, p4588_1, u1elo1]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [h4553, hlam, p4588_0]
                              · have p4588_0 := h4588c.1
                                have p4588_1 := h4588c.2.1
                                have p4588_2 := h4588c.2.2.1
                                have p4588_3 := h4588c.2.2.2
                                linarith only [hlam, p4588_0]
                            · linarith only [h4234, h4545, h4587, hlam]
                    · linarith only [h3604, h4545, h4553, hlam]
              · linarith only [h0, h4233, h4548, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4617 | h4617
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4618 | h4618
                · linarith only [h3078, h4234, h4618, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4620 | h4620
                  · linarith only [h3078, h4455, h4546, h4547, h4620, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4622 | h4622
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4623 | h4623
                      · linarith only [h3078, h4618, h4623, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4625 | h4625
                        · linarith only [h3078, h4620, h4625, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4627 | h4627
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4628 | h4628
                            · rcases h1bigk with h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c | h4629c
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h0, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3078, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3604, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3964, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4547, h4623, hc01, hc34, hlam, hphi, ht12, ht23, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4547, h4623, hc13, hc34, hlam, hphi, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4547, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3964, h4455, h4547, h4623, hc03, hc34, hlam, hphi, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hc01, hlam, hphi, p4629_1, u1elo2]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4546, hlam, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4618, hlam, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4620, hlam, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hc01, hlam, hphi, p4629_1, u1elo3]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h0, h4233, hc25, hlam, hphi, ht01, ht0b, ht5b, p4629_1, u1elo3]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4629_1, u1elo3]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3078, h4620, hc01, hlam, hphi, p4629_1, u1elo3]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4617, hc01, hlam, hphi, p4629_1, u1elo1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4617, hlam, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h3078, h4547, h4617, h4623, hc01, hc34, hlam, hphi, ht12, ht23, p4629_1]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [h4622, hlam, p4629_0]
                              · have p4629_0 := h4629c.1
                                have p4629_1 := h4629c.2.1
                                have p4629_2 := h4629c.2.2.1
                                have p4629_3 := h4629c.2.2.2
                                linarith only [hlam, p4629_0]
                            · linarith only [h0, h4547, h4623, h4628, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h3078, h4545, h4547, h4617, h4620, h4627, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h3604, h3964, h4545, h4617, h4622, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h4233, h4617, hlam]
          · linarith only [h0, h4232, h4546, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4660 | h4660
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4661 | h4661
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4662 | h4662
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4663 | h4663
                · linarith only [h3078, h4234, h4663, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4665 | h4665
                  · linarith only [h3078, h4455, h4661, h4663, h4665, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4667 | h4667
                    · linarith only [h3604, h4545, h4661, h4667, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4669 | h4669
                      · linarith only [h4232, h4234, h4669, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4671 | h4671
                        · linarith only [h0, h4232, h4665, h4671, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4673 | h4673
                          · linarith only [h4661, h4667, h4673, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4675 | h4675
                            · linarith only [h3078, h4663, h4667, h4675, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h3078, h4663, h4675, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h4233, h4662, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4679 | h4679
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4680 | h4680
                · linarith only [h3078, h4234, h4660, h4680, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4682 | h4682
                  · linarith only [h3078, h4455, h4660, h4661, h4682, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4684 | h4684
                    · linarith only [h3604, h4545, h4684, hc01, hlam, hphi, u1elo3]
                    · linarith only [h4661, h4679, h4684, hlam]
              · linarith only [h0, h3964, h4233, h4679, hc01, hlam, hphi, u1elo4]
          · linarith only [h0, h3078, h4232, h4660, hc01, hlam, hphi, u1elo2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4689 | h4689
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4690 | h4690
      · linarith only [h4232, h4233, h4690, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4692 | h4692
        · linarith only [h4232, h4233, h4689, h4692, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4694 | h4694
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4695 | h4695
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4696 | h4696
              · linarith only [h4232, h4233, h4696, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4698 | h4698
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4699 | h4699
                  · linarith only [h4689, h4690, h4694, h4696, h4699, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4701 | h4701
                    · linarith only [h3604, h4692, h4698, h4699, h4701, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4703 | h4703
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4704 | h4704
                        · linarith only [h0, h4232, h4696, h4699, h4704, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4706 | h4706
                          · linarith only [h0, h3604, h4232, h4692, h4696, h4703, h4704, h4706, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h4232, h4696, h4703, h4706, hc34, hc45, hlam, hphi]
                      · linarith only [h4689, h4690, h4703, hc23, hc35, hlam, hphi]
                · linarith only [h4689, h4690, h4698, hc13, hc35, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4711 | h4711
              · linarith only [h4232, h4233, h4689, h4695, h4711, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4713 | h4713
                · linarith only [h4694, h4695, h4713, hlam]
                · linarith only [h4689, h4690, h4713, hc13, hc35, hlam, hphi]
          · linarith only [h0, h4232, h4694, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4717 | h4717
      · linarith only [h4232, h4233, h4717, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4719 | h4719
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4720 | h4720
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4721 | h4721
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4722 | h4722
              · linarith only [h4232, h4233, h4722, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4724 | h4724
                · linarith only [h3078, h4689, h4724, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4726 | h4726
                  · linarith only [h4232, h4233, h4717, h4724, h4726, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4728 | h4728
                    · linarith only [h4721, h4722, h4728, hlam]
                    · linarith only [h3604, h3964, h4719, h4728, hc01, hlam, hphi, u1elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4731 | h4731
              · linarith only [h4232, h4233, h4731, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4733 | h4733
                · linarith only [h3078, h4689, h4733, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4735 | h4735
                  · linarith only [h3078, h4717, h4733, h4735, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4737 | h4737
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4738 | h4738
                      · linarith only [h4232, h4689, h4738, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4740 | h4740
                        · linarith only [h0, h4232, h4721, h4735, h4738, h4740, hc13, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4742 | h4742
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4743 | h4743
                            · rcases h1bigk with h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c | h4744c
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h0, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3078, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3604, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3964, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4731, h4738, h4742, hc01, hc34, hlam, hphi, ht12, ht23, p4744_1]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3078, h4731, h4738, h4742, hc01, hc34, hlam, hphi, ht12, ht23, p4744_1]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4721, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4731, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hc01, hlam, hphi, p4744_1, u1elo2]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4720, hlam, p4744_1]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4733, hlam, p4744_1]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4735, hlam, p4744_1]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hc01, hlam, hphi, p4744_1, u1elo3]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h0, h4232, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4744_1, u1elo3]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4744_1, u1elo3]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4744_1, u1elo3]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hc01, hlam, hphi, p4744_1, u1elo4]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3078, h4720, hc01, hlam, hphi, p4744_1, u1elo4]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h3078, hc01, hlam, hphi, p4744_1, u1elo4]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [h4737, hlam, p4744_0]
                              · have p4744_0 := h4744c.1
                                have p4744_1 := h4744c.2.1
                                have p4744_2 := h4744c.2.2.1
                                have p4744_3 := h4744c.2.2.2
                                linarith only [hlam, p4744_0]
                            · linarith only [h3078, h4719, h4720, h4731, h4738, h4742, h4743, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · linarith only [h3078, h3604, h4719, h4720, h4721, h4742, hc01, hlam, hphi, u1elo3]
                    · linarith only [h3604, h4719, h4737, hlam]
          · linarith only [h0, h4232, h4720, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4774 | h4774
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4775 | h4775
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4776 | h4776
              · linarith only [h4232, h4233, h4776, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4778 | h4778
                · linarith only [h3078, h4689, h4778, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4780 | h4780
                  · linarith only [h3078, h4717, h4780, hc01, hlam, hphi, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4782 | h4782
                    · linarith only [h3604, h4719, h4775, h4776, h4782, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4784 | h4784
                      · linarith only [h4232, h4689, h4784, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4786 | h4786
                        · linarith only [h0, h4232, h4776, h4780, h4786, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4788 | h4788
                          · linarith only [h4775, h4776, h4782, h4786, h4788, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4790 | h4790
                            · linarith only [h0, h4232, h4776, h4788, h4790, hc23, hc34, hlam, hphi]
                            · linarith only [h3078, h4778, h4790, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4793 | h4793
              · linarith only [h4233, h4775, h4793, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4795 | h4795
                · linarith only [h3078, h4689, h4795, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4797 | h4797
                  · linarith only [h3078, h4717, h4774, h4775, h4797, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4799 | h4799
                    · linarith only [h3078, h4689, h4719, h4799, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4801 | h4801
                      · linarith only [h0, h4232, h4775, h4795, h4799, h4801, hc13, hc45, hlam, hphi, ht34]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4803 | h4803
                        · linarith only [h3078, h4797, h4803, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4805 | h4805
                          · linarith only [h0, h4232, h4775, h4799, h4801, h4805, hc23, hc34, hlam, hphi]
                          · linarith only [h3078, h4774, h4775, h4805, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h4232, h4774, hlam]

end R2N4
