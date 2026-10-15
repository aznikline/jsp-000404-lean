import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S1
import Jsp000404.R1LeavesN7_52S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h958 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1191 | h1191
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1192 | h1192
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1193 | h1193
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1194 | h1194
        · linarith only [h1194, h3, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1196 | h1196
          · linarith only [h0, h1196, h958, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1198 | h1198
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1199 | h1199
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1200 | h1200
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1201 | h1201
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1202 | h1202
                    · rcases h0emin with h1203 | h1203 | h1203 | h1203 | h1203
                      · rcases h5bigk with h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1196, h1201, h958, hc12, hlam, hphi, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h958, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1192, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1191, h1193, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h2, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1196, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1204_1]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1, h1198, h1200, hc01, hc45, hlam, hphi, ht0b, ht5b, p1204_1]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1201, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1201, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1201, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1201, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1192, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1199, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1201, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1192, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo2]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1193, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1200, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1202, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1204_1]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [h1202, hlam, p1204_0]
                        · have p1204_0 := h1204c.1
                          have p1204_1 := h1204c.2.1
                          have p1204_2 := h1204c.2.2.1
                          have p1204_3 := h1204c.2.2.2
                          linarith only [hlam, p1204_0]
                      · linarith only [h1203, hlam, ht01, ht12, u2elo0]
                      · linarith only [h1203, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1203, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1203, h958, hlam, ht01, ht12, u2elo4]
                    · rcases h0emin with h1234 | h1234 | h1234 | h1234 | h1234
                      · rcases h5bigk with h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c | h1235c
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1191, h1193, h1200, h1202, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h958, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1191, h1193, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1191, h1193, h1202, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h2, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1196, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1235_1]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1191, h1193, h1202, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1201, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1201, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1201, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1201, h1202, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1192, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1199, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1201, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1202, hlam, p1235_1]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1193, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1200, hlam, p1235_0]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1200, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1235_1]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [h1, h1198, h1200, h1202, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1235_1, u2elo2]
                        · have p1235_0 := h1235c.1
                          have p1235_1 := h1235c.2.1
                          have p1235_2 := h1235c.2.2.1
                          have p1235_3 := h1235c.2.2.2
                          linarith only [hlam, p1235_0]
                      · linarith only [h1234, hlam, ht01, ht12, u2elo0]
                      · linarith only [h1234, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1234, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1193, h1234, h3, hlam, ht01, ht12, u2elo2]
                  · linarith only [h1192, h1201, h3, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1266 | h1266
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h1191, h1200, h1267, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases h0emin with h1269 | h1269 | h1269 | h1269 | h1269
                      · rcases h5bigk with h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c | h1270c
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1191, h1193, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h958, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1191, h1193, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1191, h1193, h1198, h1200, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h2, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1196, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1270_1]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1200, hlam, p1270_1]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo4]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo4]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1266, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1198, h1200, h1266, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1192, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1199, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1266, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1267, hlam, p1270_1]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1193, hlam, p1270_0]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1196, hc12, hc45, hlam, hphi, ht23, ht34, p1270_1]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1191, h1193, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [h1191, h1193, h1267, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1270_1, u2elo2]
                        · have p1270_0 := h1270c.1
                          have p1270_1 := h1270c.2.1
                          have p1270_2 := h1270c.2.2.1
                          have p1270_3 := h1270c.2.2.2
                          linarith only [hlam, p1270_0]
                      · linarith only [h1269, hlam, ht01, ht12, u2elo0]
                      · linarith only [h1269, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1269, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1193, h1269, h3, hlam, ht01, ht12, u2elo2]
                  · linarith only [h1192, h1266, h3, hlam]
              · linarith only [h1192, h1194, h1199, h3, hc12, hlam, hphi, u2elo2]
            · linarith only [h1191, h1194, h1198, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1303 | h1303
        · linarith only [h1303, h3, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1305 | h1305
          · linarith only [h0, h1305, h958, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1307 | h1307
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1309 | h1309
                · linarith only [h1193, h1309, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1311 | h1311
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                    · linarith only [h1191, h1193, h1312, hlam]
                    · rcases h0emin with h1314 | h1314 | h1314 | h1314 | h1314
                      · rcases h5bigk with h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1308, h958, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1315_1, u2elo4]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h958, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1192, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1315_1, u2elo2]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1193, hlam, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h2, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1305, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1309, hlam, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1315_1, u2elo4]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1315_1, u2elo4]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1311, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1315_1, u2elo2]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1193, h1311, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1315_1, u2elo2]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1192, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1308, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1311, hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hlam, p1315_0]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1312, hlam, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h0, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1305, hc12, hc45, hlam, hphi, ht23, ht34, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h0, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [h1312, hc34, hc45, hlam, hphi, p1315_1]
                        · have p1315_0 := h1315c.1
                          have p1315_1 := h1315c.2.1
                          have p1315_2 := h1315c.2.2.1
                          have p1315_3 := h1315c.2.2.2
                          linarith only [hlam, p1315_0]
                      · linarith only [h1314, h958, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1314, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1191, h1314, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1314, h958, hlam, ht01, ht12, u2elo4]
                  · linarith only [h1192, h1311, h3, hlam]
              · linarith only [h1192, h1303, h1308, h3, hc12, hlam, hphi, u2elo2]
            · linarith only [h1191, h1303, h1307, h3, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1348 | h1348
      · linarith only [h1191, h1192, h1348, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1350 | h1350
        · linarith only [h0, h1350, h3, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
          · linarith only [h0, h1191, h1192, h1352, h3, h958, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1354 | h1354
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1355 | h1355
              · linarith only [h1, h1192, h1355, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1357 | h1357
                · linarith only [h1, h1192, h1348, h1354, h1357, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1359 | h1359
                  · linarith only [h1192, h1359, h3, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1361 | h1361
                    · linarith only [h1191, h1348, h1361, hlam]
                    · rcases h0emin with h1363 | h1363 | h1363 | h1363 | h1363
                      · rcases h5bigk with h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h958, hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1192, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1348, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h2, hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1352, hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1355, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1357, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1364_1, u2elo4]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1364_1, u2elo4]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1359, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1359, h1361, h3, hc02, hlam, hphi, p1364_1, u2elo4]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, h2, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, h1361, hc34, hc45, hlam, hphi, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h0, h1361, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hlam, p1364_0]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1361, hlam, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, h2, hc34, hc45, hlam, hphi, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1354, h1355, hc34, hc45, hlam, hphi, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h0, h1359, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [h1, h1192, h1354, hc34, hc45, hlam, hphi, p1364_1]
                        · have p1364_0 := h1364c.1
                          have p1364_1 := h1364c.2.1
                          have p1364_2 := h1364c.2.2.1
                          have p1364_3 := h1364c.2.2.2
                          linarith only [hlam, p1364_0]
                      · linarith only [h1363, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1359, h1363, h3, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1191, h1359, h1363, h3, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1363, h958, hlam, ht01, ht12, u2elo4]
            · linarith only [h1191, h1192, h1354, hc13, hc35, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1395 | h1395
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1396 | h1396
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1397 | h1397
        · linarith only [h0, h1397, h3, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1399 | h1399
          · linarith only [h0, h1399, h958, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1401 | h1401
            · linarith only [h1, h1191, h1395, h1401, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1403 | h1403
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1404 | h1404
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1405 | h1405
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                    · rcases h0emin with h1407 | h1407 | h1407 | h1407 | h1407
                      · rcases h5bigk with h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1191, h1395, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h958, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1191, h1395, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1191, h1395, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h2, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1399, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1406, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1191, h1395, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1408_1, u2elo4]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1408_1, u2elo4]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1405, h1406, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1408_1, u2elo2]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1408_1, u2elo2]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1395, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1403, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1405, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1191, h1395, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1396, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1404, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h0, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1408_1]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [h1406, hlam, p1408_0]
                        · have p1408_0 := h1408c.1
                          have p1408_1 := h1408c.2.1
                          have p1408_2 := h1408c.2.2.1
                          have p1408_3 := h1408c.2.2.2
                          linarith only [hlam, p1408_0]
                      · linarith only [h1407, hlam, ht01, ht12, u2elo0]
                      · linarith only [h1191, h1407, hc34, hlam, ht01, ht12, ht23]
                      · rcases h5bigk with h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1399, h1405, h958, hc12, hlam, hphi, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h958, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, h958, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h2, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1399, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1406, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, h2, h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, h1406, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1436_1, u2elo2]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1395, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1403, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1405, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1191, h1395, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1396, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1404, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h0, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1406, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                      · linarith only [h1407, h958, hlam, ht01, ht12, u2elo4]
                    · linarith only [h1191, h1395, h1404, h1406, h2, hlam]
                  · linarith only [h1, h1191, h1403, h1405, hc23, hc34, hlam, hphi]
                · linarith only [h1401, h1403, h1404, hlam]
              · linarith only [h1191, h1395, h1403, hc13, hc34, hlam, hphi]
      · linarith only [h1191, h1395, h1396, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
        · linarith only [h0, h1469, h3, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1471 | h1471
          · linarith only [h0, h1471, h958, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
            · linarith only [h1, h1191, h1473, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1475 | h1475
              · linarith only [h1, h1395, h1475, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1477 | h1477
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1478 | h1478
                  · linarith only [h1395, h1478, h3, hc02, hlam, hphi, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1480 | h1480
                    · rcases h0emin with h1481 | h1481 | h1481 | h1481 | h1481
                      · rcases h5bigk with h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1482_1, u2elo4]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h958, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1395, hlam, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1482_1, u2elo4]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h2, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1471, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1475, hlam, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1482_1, u2elo4]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1482_1, u2elo4]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1478, hlam, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1482_1, u2elo4]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1469, h1475, h1480, h2, hc12, hc34, hlam, hphi, ht23, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1469, h1475, h1480, hc12, hc34, hlam, hphi, ht23, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h0, h1480, h958, hc12, hc34, hlam, hphi, ht23, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          rcases p1482_3 (m.d 0 5) (by simp) with h1502 | h1502
                          · linarith only [h1395, h1502, hlam]
                          · linarith only [h1468, h1502, hlam]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1468, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1477, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h0, h1477, h1478, h3, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1482_1]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [h1480, hlam, p1482_0]
                        · have p1482_0 := h1482c.1
                          have p1482_1 := h1482c.2.1
                          have p1482_2 := h1482c.2.2.1
                          have p1482_3 := h1482c.2.2.2
                          linarith only [hlam, p1482_0]
                      · linarith only [h1481, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1478, h1481, h3, hlam, ht01, ht12, u2elo4]
                      · rcases h5bigk with h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1469, h1475, h958, hc12, hlam, hphi, p1512_1, u2elo4]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h958, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1395, hlam, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, u2elo4]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h2, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1471, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1475, hlam, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, u2elo4]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, u2elo4]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1478, hlam, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, u2elo4]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1469, h1475, h1480, h2, hc12, hc34, hlam, hphi, ht23, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1469, h1475, h1480, hc12, hc34, hlam, hphi, ht23, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1480, h958, hc02, hc34, hlam, hphi, ht23, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          rcases p1512_3 (m.d 0 5) (by simp) with h1532 | h1532
                          · linarith only [h1395, h1532, hlam]
                          · linarith only [h1468, h1532, hlam]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1468, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1477, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1478, hc23, hc45, hlam, hphi, ht34, p1512_1]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [h1480, hlam, p1512_0]
                        · have p1512_0 := h1512c.1
                          have p1512_1 := h1512c.2.1
                          have p1512_2 := h1512c.2.2.1
                          have p1512_3 := h1512c.2.2.2
                          linarith only [hlam, p1512_0]
                      · linarith only [h1481, h958, hlam, ht01, ht12, u2elo4]
                    · linarith only [h1191, h1468, h1480, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1542 | h1542
                  · linarith only [h1, h1395, h1469, h1542, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1544 | h1544
                    · rcases h0emin with h1545 | h1545 | h1545 | h1545 | h1545
                      · rcases h5bigk with h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1546_1, u2elo4]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h958, hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1395, hlam, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1469, h1473, h1477, h958, hc12, hlam, hphi, p1546_1, u2elo4]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h2, hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1471, hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1475, hlam, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1477, hlam, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1546_1, u2elo4]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1546_1, u2elo4]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1542, hlam, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1469, h1473, h1477, hc12, hlam, hphi, p1546_1, u2elo4]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1468, h1469, h1473, h1477, hc12, hc35, hlam, hphi, ht23, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1469, h1473, h1477, hc12, hc35, hlam, hphi, ht23, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h0, h958, hc12, hc35, hlam, hphi, ht23, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1469, h1473, h1477, h1544, hc12, hc34, hlam, hphi, ht23, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1468, hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1468, h1469, h1473, h1477, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1468, h958, hlam, p1546_1]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [h1544, hlam, p1546_0]
                        · have p1546_0 := h1546c.1
                          have p1546_1 := h1546c.2.1
                          have p1546_2 := h1546c.2.2.1
                          have p1546_3 := h1546c.2.2.2
                          linarith only [hlam, p1546_0]
                      · linarith only [h1545, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1545, h3, hlam, ht01, ht12, u2elo2]
                      · rcases h5bigk with h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c | h1574c
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, h958, hc12, hlam, hphi, p1574_1, u2elo4]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h958, hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1395, hlam, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h958, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1574_1, u2elo4]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h2, hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1471, hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1475, hlam, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1477, hlam, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1574_1, u2elo4]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, hc12, hlam, hphi, p1574_1, u2elo4]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1542, hlam, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, hc12, hlam, hphi, p1574_1, u2elo4]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1468, h1469, h1473, h1477, h1544, hc12, hc34, hlam, hphi, ht23, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, h1544, hc12, hc34, hlam, hphi, ht23, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1544, h958, hc02, hc34, hlam, hphi, ht23, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, h1544, hc12, hc34, hlam, hphi, ht23, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1468, hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1469, h1473, h1477, hc12, hc45, hlam, hphi, ht23, ht34, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1468, h958, hlam, p1574_1]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [h1544, hlam, p1574_0]
                        · have p1574_0 := h1574c.1
                          have p1574_1 := h1574c.2.1
                          have p1574_2 := h1574c.2.2.1
                          have p1574_3 := h1574c.2.2.2
                          linarith only [hlam, p1574_0]
                      · linarith only [h1545, h958, hlam, ht01, ht12, u2elo4]
                    · linarith only [h1, h1191, h1468, h1469, h1544, h958, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1602 | h1602
        · linarith only [h0, h1602, h3, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1604 | h1604
          · linarith only [h0, h1604, h958, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1606 | h1606
            · linarith only [h1, h1191, h1606, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1608 | h1608
              · linarith only [h1, h1395, h1608, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1610 | h1610
                · linarith only [h1468, h1610, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1612 | h1612
                  · linarith only [h0, h1395, h1612, h3, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1614 | h1614
                    · rcases h0emin with h1615 | h1615 | h1615 | h1615 | h1615
                      · rcases h5bigk with h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h958, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1616_1, u2elo4]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h958, hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1395, hlam, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1468, hlam, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h2, hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1604, hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1608, hlam, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1610, hlam, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1616_1, u2elo4]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1616_1, u2elo4]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1612, hlam, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1191, h1468, h3, hc12, hlam, hphi, p1616_1, u2elo4]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1191, h1468, h1614, h3, hc12, hc34, hlam, hphi, ht23, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1606, h1610, h1614, hc13, hc34, hlam, hphi, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1614, h958, hc12, hc34, hlam, hphi, ht23, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1191, h1468, h1614, h3, hc12, hc34, hlam, hphi, ht23, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1191, h1468, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1602, h1606, h1610, hc12, hc45, hlam, hphi, ht23, ht34, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h0, h1612, h1614, h3, hc12, hc34, hlam, hphi, ht23, p1616_1]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [h1614, hlam, p1616_0]
                        · have p1616_0 := h1616c.1
                          have p1616_1 := h1616c.2.1
                          have p1616_2 := h1616c.2.2.1
                          have p1616_3 := h1616c.2.2.2
                          linarith only [hlam, p1616_0]
                      · linarith only [h1615, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1612, h1615, h3, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1468, h1615, h958, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1615, h958, hlam, ht01, ht12, u2elo4]
                    · rcases h0emin with h1646 | h1646 | h1646 | h1646 | h1646
                      · rcases h5bigk with h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, h958, hc12, hlam, hphi, p1647_1, u2elo4]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h958, hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1395, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1468, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h2, hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1604, hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1608, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1610, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1647_1, u2elo4]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, hc12, hlam, hphi, p1647_1, u2elo4]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1612, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1612, h1614, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1647_1, u2elo4]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, h2, hc12, hc35, hlam, hphi, ht23, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, h1614, hc12, hc45, hlam, hphi, ht23, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h0, h1614, h958, hc12, hc45, hlam, hphi, ht23, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hlam, p1647_0]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1614, hlam, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1602, h1606, h1610, hc12, hc45, hlam, hphi, ht23, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h0, h1612, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [h1395, hc03, hc45, hlam, hphi, ht34, p1647_1]
                        · have p1647_0 := h1647c.1
                          have p1647_1 := h1647c.2.1
                          have p1647_2 := h1647c.2.2.1
                          have p1647_3 := h1647c.2.2.2
                          linarith only [hlam, p1647_0]
                      · linarith only [h1646, h3, hlam, ht01, ht12, u2elo2]
                      · linarith only [h1395, h1646, hc35, hlam, ht01, ht12, ht23]
                      · linarith only [h1468, h1646, h958, hlam, ht01, ht12, u2elo4]
                      · linarith only [h1646, h958, hlam, ht01, ht12, u2elo4]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h958 | h958
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h958
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h958

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1677 | h1677
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1678 | h1678
    · linarith only [h0, h1678, h2, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1680 | h1680
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1681 | h1681
        · linarith only [h0, h1677, h1681, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1683 | h1683
          · linarith only [h0, h1677, h1680, h1683, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1685 | h1685
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1686 | h1686
              · linarith only [h0, h1678, h1686, h2, hlam]
              · linarith only [h0, h1685, h1686, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h1677, h1685, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1690 | h1690
        · linarith only [h1, h1690, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1692 | h1692
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1693 | h1693
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1694 | h1694
              · linarith only [h0, h1678, h1694, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1693, h1694, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h0, h1677, h1678, h1693, h2, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1698 | h1698
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1699 | h1699
              · linarith only [h1678, h1699, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1698, h1699, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h1677, h1678, h1698, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1703 | h1703
    · linarith only [h1, h1677, h1703, h2, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1705 | h1705
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1706 | h1706
        · linarith only [h1, h1706, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1708 | h1708
          · linarith only [h1, h1705, h1708, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1710 | h1710
            · linarith only [h0, h1677, h1710, h2, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1712 | h1712
              · linarith only [h0, h1703, h1712, h2, hlam]
              · linarith only [h1, h1710, h1712, h2, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1715 | h1715
        · linarith only [h1, h1715, h2, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1717 | h1717
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1718 | h1718
            · linarith only [h1677, h1718, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1720 | h1720
              · linarith only [h0, h1703, h1720, hlam]
              · linarith only [h1, h1718, h1720, h2, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
            · linarith only [h0, h1677, h1723, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1725 | h1725
              · linarith only [h0, h1703, h1725, hlam]
              · linarith only [h1, h1723, h1725, h2, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1728 | h1728
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1729 | h1729
    · linarith only [h0, h1, h1729, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1731 | h1731
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1732 | h1732
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1733 | h1733
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1734 | h1734
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1735 | h1735
              · linarith only [h1729, h1731, h1735, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h1, h1735, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
              · linarith only [h0, h1, h1729, h1738, hlam]
              · linarith only [h0, h1, h1738, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h1731, h1733, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1742 | h1742
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1743 | h1743
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1744 | h1744
              · linarith only [h0, h1, h1732, h1744, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h1744, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h1729, h1731, h1732, h1743, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h1729, h1731, h1742, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1749 | h1749
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1750 | h1750
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1751 | h1751
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1752 | h1752
              · linarith only [h0, h1, h1729, h1752, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h1752, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
              · linarith only [h0, h1, h1729, h1750, h1755, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h0, h1, h1755, hc12, hlam, hphi, u2elo2]
          · linarith only [h1, h1728, h1750, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1759 | h1759
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1760 | h1760
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1761 | h1761
              · linarith only [h0, h1, h1749, h1761, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h1761, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1728, h1749, h1760, hlam]
          · linarith only [h1, h1728, h1759, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1766 | h1766
    · linarith only [h0, h1, h1766, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1768 | h1768
      · linarith only [h0, h1728, h1768, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1770 | h1770
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1771 | h1771
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1772 | h1772
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1773 | h1773
              · linarith only [h0, h1, h1766, h1773, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h1773, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1776 | h1776
              · linarith only [h0, h1, h1766, h1770, h1776, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h0, h1, h1776, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1779 | h1779
            · linarith only [h1770, h1771, h1779, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1781 | h1781
              · linarith only [h0, h1, h1771, h1781, hc23, hc35, hlam, hphi]
              · linarith only [h0, h1, h1781, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1784 | h1784
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1785 | h1785
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1786 | h1786
              · linarith only [h0, h1728, h1770, h1784, h1786, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h1786, hc12, hlam, hphi, u2elo2]
            · linarith only [h1770, h1784, h1785, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1790 | h1790
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1791 | h1791
              · linarith only [h0, h1, h1770, h1791, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h1791, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
              · linarith only [h0, h1, h1770, h1794, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h1794, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0 m hb0 hb2 hb5 h0 h1
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x1 m hb0 hb2 hb5 h0 h1

end R2N4
