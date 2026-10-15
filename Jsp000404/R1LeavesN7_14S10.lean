import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S8
import Jsp000404.R1LeavesN7_14S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8059 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8881 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 4 5 (by decide) (by decide) with h9003 | h9003
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9004 | h9004
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9005 | h9005
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9006 | h9006
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9007 | h9007
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9008 | h9008
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9009 | h9009
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9010 | h9010
                · linarith only [h8056, h8059, h9010, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9012 | h9012
                  · linarith only [h8056, h8881, h9012, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9014 | h9014
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9015 | h9015
                      · rcases h0bigk with h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c | h9016c
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h0, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h4610, hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h6681, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h7494, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          rcases p9016_3 (m.d 0 1) (by simp) with h9022 | h9022
                          · linarith only [h0, h9022, hlam]
                          · rcases p9016_3 (m.d 0 2) (by simp) with h9024 | h9024
                            · rcases p9016_3 (m.d 0 3) (by simp) with h9025 | h9025
                              · linarith only [h8056, h9025, hlam]
                              · linarith only [h4610, h9025, hlam]
                            · linarith only [h0, h9024, hlam]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          rcases p9016_3 (m.d 0 1) (by simp) with h9030 | h9030
                          · linarith only [h0, h9030, hlam]
                          · rcases p9016_3 (m.d 0 2) (by simp) with h9032 | h9032
                            · rcases p9016_3 (m.d 0 3) (by simp) with h9033 | h9033
                              · linarith only [h8056, h9033, hlam]
                              · rcases p9016_3 (m.d 0 4) (by simp) with h9035 | h9035
                                · linarith only [h8057, h9035, hlam]
                                · linarith only [h8059, h9035, hlam]
                            · linarith only [h8056, h9032, hlam]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8057, h9014, hc45, hlam, hphi, ht0b, ht5b, p9016_1, u0elo1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          rcases p9016_3 (m.d 0 1) (by simp) with h9040 | h9040
                          · linarith only [h0, h9040, hlam]
                          · rcases p9016_3 (m.d 0 2) (by simp) with h9042 | h9042
                            · rcases p9016_3 (m.d 0 3) (by simp) with h9043 | h9043
                              · linarith only [h8056, h9043, hlam]
                              · rcases p9016_3 (m.d 0 4) (by simp) with h9045 | h9045
                                · linarith only [h8057, h9045, hlam]
                                · linarith only [h9003, h9045, hlam]
                            · linarith only [h8058, h9042, hlam]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8881, h9004, h9007, h9015, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8056, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8059, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8881, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8059, h9004, h9007, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8057, hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h4610, h8059, h9004, h9007, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [hlam, p9016_0]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h4610, h8059, h8881, h9004, h9007, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8881, h9004, h9007, h9015, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h8058, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h4610, h8881, h9004, h9007, h9015, hc01, hc12, hlam, hphi, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [h9003, hlam, p9016_1]
                        · have p9016_0 := h9016c.1
                          have p9016_1 := h9016c.2.1
                          have p9016_2 := h9016c.2.2.1
                          have p9016_3 := h9016c.2.2.2
                          linarith only [hlam, p9016_0]
                      · linarith only [h8059, h9003, h9015, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9065 | h9065
                      · rcases h0bigk with h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c | h9066c
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h0, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h4610, hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h6681, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h7494, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          rcases p9066_3 (m.d 0 1) (by simp) with h9072 | h9072
                          · linarith only [h0, h9072, hlam]
                          · rcases p9066_3 (m.d 0 2) (by simp) with h9074 | h9074
                            · rcases p9066_3 (m.d 0 3) (by simp) with h9075 | h9075
                              · linarith only [h8056, h9075, hlam]
                              · linarith only [h4610, h9075, hlam]
                            · linarith only [h0, h9074, hlam]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          rcases p9066_3 (m.d 0 1) (by simp) with h9080 | h9080
                          · linarith only [h0, h9080, hlam]
                          · rcases p9066_3 (m.d 0 2) (by simp) with h9082 | h9082
                            · rcases p9066_3 (m.d 0 3) (by simp) with h9083 | h9083
                              · linarith only [h8056, h9083, hlam]
                              · rcases p9066_3 (m.d 0 4) (by simp) with h9085 | h9085
                                · linarith only [h8057, h9085, hlam]
                                · linarith only [h8059, h9085, hlam]
                            · linarith only [h8056, h9082, hlam]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h9003, h9010, h9014, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9066_1, u0elo1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h9003, h9010, h9014, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9066_1, u0elo1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8881, h9008, hc01, hc15, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8056, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8059, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8881, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8059, h9004, h9007, hc01, hc12, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8057, hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h4610, h8059, h9004, h9007, hc01, hc12, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [hlam, p9066_0]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h7494, h8059, h9004, h9007, hc01, hc12, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8059, h9003, h9004, h9007, hc01, hc12, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h8058, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h4610, h8059, h9003, h9004, h9007, hc01, hc12, hlam, hphi, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [h9003, hlam, p9066_1]
                        · have p9066_0 := h9066c.1
                          have p9066_1 := h9066c.2.1
                          have p9066_2 := h9066c.2.2.1
                          have p9066_3 := h9066c.2.2.2
                          linarith only [hlam, p9066_0]
                      · linarith only [h8059, h9003, h9065, hlam]
              · linarith only [h8059, h9003, h9007, h9009, hlam]
            · linarith only [h4610, h8059, h9007, h9008, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9109 | h9109
            · linarith only [h4610, h8881, h9007, h9109, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9111 | h9111
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9112 | h9112
                · linarith only [h4610, h9007, h9112, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9114 | h9114
                  · linarith only [h4610, h8056, h9109, h9114, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9116 | h9116
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9117 | h9117
                      · rcases h0bigk with h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c | h9118c
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h0, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h4610, hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h6681, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h7494, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9124 | h9124
                          · linarith only [h0, h9124, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9126 | h9126
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9127 | h9127
                              · linarith only [h8056, h9127, hlam]
                              · linarith only [h4610, h9127, hlam]
                            · linarith only [h0, h9126, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9132 | h9132
                          · linarith only [h0, h9132, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9134 | h9134
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9135 | h9135
                              · linarith only [h8056, h9135, hlam]
                              · rcases p9118_3 (m.d 0 4) (by simp) with h9137 | h9137
                                · linarith only [h8057, h9137, hlam]
                                · linarith only [h8059, h9137, hlam]
                            · linarith only [h8056, h9134, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8057, h9116, hc45, hlam, hphi, ht0b, ht5b, p9118_1, u0elo1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9142 | h9142
                          · linarith only [h0, h9142, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9144 | h9144
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9145 | h9145
                              · linarith only [h8056, h9145, hlam]
                              · rcases p9118_3 (m.d 0 4) (by simp) with h9147 | h9147
                                · linarith only [h8057, h9147, hlam]
                                · linarith only [h9003, h9147, hlam]
                            · linarith only [h8058, h9144, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h4610, h9109, h9117, hc01, hc34, hlam, hphi, ht12, ht23, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8056, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8059, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8881, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9156 | h9156
                          · linarith only [h6681, h9156, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9158 | h9158
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9159 | h9159
                              · linarith only [h8059, h9159, hlam]
                              · linarith only [h4610, h9159, hlam]
                            · linarith only [h0, h9158, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8057, hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9164 | h9164
                          · linarith only [h6681, h9164, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9166 | h9166
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9167 | h9167
                              · linarith only [h8059, h9167, hlam]
                              · rcases p9118_3 (m.d 0 4) (by simp) with h9169 | h9169
                                · rcases p9118_3 (m.d 0 5) (by simp) with h9170 | h9170
                                  · linarith only [h9003, h9170, hlam]
                                  · linarith only [h8881, h9170, hlam]
                                · linarith only [h8059, h9169, hlam]
                            · linarith only [h8056, h9166, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [hlam, p9118_0]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9176 | h9176
                          · linarith only [h6681, h9176, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9178 | h9178
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9179 | h9179
                              · linarith only [h8059, h9179, hlam]
                              · rcases p9118_3 (m.d 0 4) (by simp) with h9181 | h9181
                                · rcases p9118_3 (m.d 0 5) (by simp) with h9182 | h9182
                                  · linarith only [h9003, h9182, hlam]
                                  · rcases h2bigk with h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c | h9184c
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h0, hlam, p9184_1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      rcases p9184_3 (m.d 0 2) (by simp) with h9187 | h9187
                                      · rcases p9184_3 (m.d 1 2) (by simp) with h9188 | h9188
                                        · rcases p9184_3 (m.d 2 3) (by simp) with h9189 | h9189
                                          · linarith only [h9189, hlam, p9184_0]
                                          · rcases p9184_3 (m.d 2 4) (by simp) with h9191 | h9191
                                            · linarith only [h8057, h9191, hlam]
                                            · linarith only [h9112, h9191, hlam]
                                        · linarith only [h9004, h9188, hlam]
                                      · linarith only [h9187, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9116, hc45, hlam, hphi, ht0b, ht5b, p9184_1, u0elo1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      rcases p9184_3 (m.d 0 2) (by simp) with h9197 | h9197
                                      · rcases p9184_3 (m.d 1 2) (by simp) with h9198 | h9198
                                        · rcases p9184_3 (m.d 2 3) (by simp) with h9199 | h9199
                                          · linarith only [h8056, h9199, hlam]
                                          · rcases p9184_3 (m.d 2 4) (by simp) with h9201 | h9201
                                            · linarith only [h8057, h9201, hlam]
                                            · linarith only [h9116, h9201, hlam]
                                        · linarith only [h9006, h9198, hlam]
                                      · linarith only [h9197, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8057, h9116, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9184_1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      rcases p9184_3 (m.d 0 2) (by simp) with h9208 | h9208
                                      · linarith only [h0, h9208, hlam]
                                      · linarith only [h8056, h9208, hlam]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      rcases p9184_3 (m.d 0 2) (by simp) with h9211 | h9211
                                      · linarith only [h0, h9211, hlam]
                                      · linarith only [h8057, h9211, hlam]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      rcases p9184_3 (m.d 0 2) (by simp) with h9214 | h9214
                                      · linarith only [h0, h9214, hlam]
                                      · linarith only [h8058, h9214, hlam]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8056, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9004, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9112, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9114, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8057, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9005, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9184_1, u0elo1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8057, hc25, hlam, hphi, ht0b, ht5b, p9184_1, u0elo1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8058, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9006, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9184_1, u0elo1]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [h9116, hlam, p9184_0]
                                    · have p9184_0 := h9184c.1
                                      have p9184_1 := h9184c.2.1
                                      have p9184_2 := h9184c.2.2.1
                                      have p9184_3 := h9184c.2.2.2
                                      linarith only [hlam, p9184_0]
                                · linarith only [h9003, h9181, hlam]
                            · linarith only [h8058, h9178, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9234 | h9234
                          · linarith only [h7494, h9234, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9236 | h9236
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9237 | h9237
                              · linarith only [h8881, h9237, hlam]
                              · linarith only [h4610, h9237, hlam]
                            · linarith only [h0, h9236, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h8058, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          rcases p9118_3 (m.d 0 1) (by simp) with h9242 | h9242
                          · linarith only [h7494, h9242, hlam]
                          · rcases p9118_3 (m.d 0 2) (by simp) with h9244 | h9244
                            · rcases p9118_3 (m.d 0 3) (by simp) with h9245 | h9245
                              · linarith only [h8881, h9245, hlam]
                              · rcases p9118_3 (m.d 0 4) (by simp) with h9247 | h9247
                                · rcases p9118_3 (m.d 0 5) (by simp) with h9248 | h9248
                                  · rcases h2bigk with h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c | h9249c
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h0, hlam, p9249_1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      rcases p9249_3 (m.d 0 2) (by simp) with h9252 | h9252
                                      · rcases p9249_3 (m.d 1 2) (by simp) with h9253 | h9253
                                        · rcases p9249_3 (m.d 2 3) (by simp) with h9254 | h9254
                                          · linarith only [h9254, hlam, p9249_0]
                                          · rcases p9249_3 (m.d 2 4) (by simp) with h9256 | h9256
                                            · linarith only [h8057, h9256, hlam]
                                            · linarith only [h9112, h9256, hlam]
                                        · linarith only [h9004, h9253, hlam]
                                      · linarith only [h9252, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9116, hc45, hlam, hphi, ht0b, ht5b, p9249_1, u0elo1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      rcases p9249_3 (m.d 0 2) (by simp) with h9262 | h9262
                                      · rcases p9249_3 (m.d 1 2) (by simp) with h9263 | h9263
                                        · rcases p9249_3 (m.d 2 3) (by simp) with h9264 | h9264
                                          · linarith only [h8056, h9264, hlam]
                                          · rcases p9249_3 (m.d 2 4) (by simp) with h9266 | h9266
                                            · linarith only [h8057, h9266, hlam]
                                            · linarith only [h9116, h9266, hlam]
                                        · linarith only [h9006, h9263, hlam]
                                      · linarith only [h9262, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8057, h9116, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9249_1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      rcases p9249_3 (m.d 0 2) (by simp) with h9273 | h9273
                                      · linarith only [h0, h9273, hlam]
                                      · linarith only [h8056, h9273, hlam]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      rcases p9249_3 (m.d 0 2) (by simp) with h9276 | h9276
                                      · linarith only [h0, h9276, hlam]
                                      · linarith only [h8057, h9276, hlam]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      rcases p9249_3 (m.d 0 2) (by simp) with h9279 | h9279
                                      · linarith only [h0, h9279, hlam]
                                      · linarith only [h8058, h9279, hlam]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8056, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9004, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9112, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9114, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8057, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9005, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9249_1, u0elo1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8057, h9114, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9249_1, u0elo1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8058, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9006, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9249_1, u0elo1]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [h9116, hlam, p9249_0]
                                    · have p9249_0 := h9249c.1
                                      have p9249_1 := h9249c.2.1
                                      have p9249_2 := h9249c.2.2.1
                                      have p9249_3 := h9249c.2.2.2
                                      linarith only [hlam, p9249_0]
                                  · linarith only [h8881, h9248, hlam]
                                · linarith only [h8059, h9247, hlam]
                            · linarith only [h8056, h9244, hlam]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [h9003, hlam, p9118_1]
                        · have p9118_0 := h9118c.1
                          have p9118_1 := h9118c.2.1
                          have p9118_2 := h9118c.2.2.1
                          have p9118_3 := h9118c.2.2.2
                          linarith only [hlam, p9118_0]
                      · linarith only [h8059, h9003, h9117, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9303 | h9303
                      · rcases h0bigk with h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c | h9304c
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h0, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h4610, hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h6681, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h7494, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9310 | h9310
                          · linarith only [h0, h9310, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9312 | h9312
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9313 | h9313
                              · linarith only [h8056, h9313, hlam]
                              · linarith only [h4610, h9313, hlam]
                            · linarith only [h0, h9312, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9318 | h9318
                          · linarith only [h0, h9318, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9320 | h9320
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9321 | h9321
                              · linarith only [h8056, h9321, hlam]
                              · rcases p9304_3 (m.d 0 4) (by simp) with h9323 | h9323
                                · linarith only [h8057, h9323, hlam]
                                · linarith only [h8059, h9323, hlam]
                            · linarith only [h8056, h9320, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h9003, h9112, h9116, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9304_1, u0elo1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h9003, h9112, h9116, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9304_1, u0elo1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h4610, h9109, h9303, hc01, hc34, hlam, hphi, ht12, ht23, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8056, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8059, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8881, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9334 | h9334
                          · linarith only [h6681, h9334, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9336 | h9336
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9337 | h9337
                              · linarith only [h8059, h9337, hlam]
                              · linarith only [h4610, h9337, hlam]
                            · linarith only [h0, h9336, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8057, hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9342 | h9342
                          · linarith only [h6681, h9342, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9344 | h9344
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9345 | h9345
                              · linarith only [h8059, h9345, hlam]
                              · rcases p9304_3 (m.d 0 4) (by simp) with h9347 | h9347
                                · rcases p9304_3 (m.d 0 5) (by simp) with h9348 | h9348
                                  · linarith only [h9003, h9348, hlam]
                                  · linarith only [h8881, h9348, hlam]
                                · linarith only [h8059, h9347, hlam]
                            · linarith only [h8056, h9344, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [hlam, p9304_0]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8057, h9003, h9112, h9116, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9304_1, u0elo1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9355 | h9355
                          · linarith only [h7494, h9355, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9357 | h9357
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9358 | h9358
                              · linarith only [h8881, h9358, hlam]
                              · linarith only [h4610, h9358, hlam]
                            · linarith only [h0, h9357, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h8058, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          rcases p9304_3 (m.d 0 1) (by simp) with h9363 | h9363
                          · linarith only [h7494, h9363, hlam]
                          · rcases p9304_3 (m.d 0 2) (by simp) with h9365 | h9365
                            · rcases p9304_3 (m.d 0 3) (by simp) with h9366 | h9366
                              · linarith only [h8881, h9366, hlam]
                              · rcases p9304_3 (m.d 0 4) (by simp) with h9368 | h9368
                                · rcases p9304_3 (m.d 0 5) (by simp) with h9369 | h9369
                                  · rcases h2bigk with h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c | h9370c
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h0, hlam, p9370_1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9373 | h9373
                                      · rcases p9370_3 (m.d 1 2) (by simp) with h9374 | h9374
                                        · rcases p9370_3 (m.d 2 3) (by simp) with h9375 | h9375
                                          · linarith only [h9375, hlam, p9370_0]
                                          · rcases p9370_3 (m.d 2 4) (by simp) with h9377 | h9377
                                            · linarith only [h8057, h9377, hlam]
                                            · linarith only [h9112, h9377, hlam]
                                        · linarith only [h9004, h9374, hlam]
                                      · linarith only [h9373, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9382 | h9382
                                      · rcases p9370_3 (m.d 1 2) (by simp) with h9383 | h9383
                                        · rcases p9370_3 (m.d 2 3) (by simp) with h9384 | h9384
                                          · linarith only [h8056, h9384, hlam]
                                          · rcases p9370_3 (m.d 2 4) (by simp) with h9386 | h9386
                                            · linarith only [h9386, hlam, p9370_0]
                                            · rcases p9370_3 (m.d 2 5) (by simp) with h9388 | h9388
                                              · linarith only [h8058, h9388, hlam]
                                              · linarith only [h9116, h9388, hlam]
                                        · linarith only [h9005, h9383, hlam]
                                      · linarith only [h9382, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9393 | h9393
                                      · rcases p9370_3 (m.d 1 2) (by simp) with h9394 | h9394
                                        · rcases p9370_3 (m.d 2 3) (by simp) with h9395 | h9395
                                          · linarith only [h8056, h9395, hlam]
                                          · rcases p9370_3 (m.d 2 4) (by simp) with h9397 | h9397
                                            · linarith only [h8057, h9397, hlam]
                                            · rcases p9370_3 (m.d 2 5) (by simp) with h9399 | h9399
                                              · linarith only [h9399, hlam, p9370_0]
                                              · rcases h3bigk with h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c | h9401c
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h4610, hlam, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9304_1, p9401_1, u0elo4]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h8059, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h8881, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9109, h9303, hc03, hc34, hlam, hphi, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9109, h9303, hc23, hc34, hlam, hphi, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9007, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9109, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h8056, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9004, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9112, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9114, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  rcases p9401_3 (m.d 0 3) (by simp) with h9417 | h9417
                                                  · linarith only [h9417, hlam, p9401_0]
                                                  · rcases p9401_3 (m.d 1 3) (by simp) with h9419 | h9419
                                                    · linarith only [h9007, h9419, hlam]
                                                    · linarith only [h4610, h9419, hlam]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h4610, hc01, hc34, hlam, hphi, ht12, ht23, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  rcases p9401_3 (m.d 0 3) (by simp) with h9423 | h9423
                                                  · linarith only [h8059, h9423, hlam]
                                                  · linarith only [h8056, h9423, hlam]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h4610, h8881, hc01, hc34, hlam, hphi, ht12, ht23, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  rcases p9401_3 (m.d 0 3) (by simp) with h9428 | h9428
                                                  · linarith only [h9428, hlam, p9401_0]
                                                  · rcases p9401_3 (m.d 1 3) (by simp) with h9430 | h9430
                                                    · linarith only [h9109, h9430, hlam]
                                                    · linarith only [h4610, h9430, hlam]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h4610, hc01, hc35, hlam, hphi, ht12, ht23, p9401_1]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  rcases p9401_3 (m.d 0 3) (by simp) with h9434 | h9434
                                                  · linarith only [h8881, h9434, hlam]
                                                  · linarith only [h8056, h9434, hlam]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [h9303, hlam, p9401_0]
                                                · have p9401_0 := h9401c.1
                                                  have p9401_1 := h9401c.2.1
                                                  have p9401_2 := h9401c.2.2.1
                                                  have p9401_3 := h9401c.2.2.2
                                                  linarith only [hlam, p9401_0]
                                        · linarith only [h9006, h9394, hlam]
                                      · linarith only [h9393, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h4610, h8057, h9003, hc01, hc12, hlam, hphi, p9304_1, p9370_1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9443 | h9443
                                      · linarith only [h0, h9443, hlam]
                                      · linarith only [h8056, h9443, hlam]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9446 | h9446
                                      · linarith only [h0, h9446, hlam]
                                      · linarith only [h8057, h9446, hlam]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      rcases p9370_3 (m.d 0 2) (by simp) with h9449 | h9449
                                      · linarith only [h0, h9449, hlam]
                                      · linarith only [h8058, h9449, hlam]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h8056, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9004, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9112, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9114, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h8057, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9005, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9116, hc23, hc45, hlam, hphi, ht34, p9370_1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9116, hlam, p9370_1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h8058, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h9006, hlam, p9370_0]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9370_1, u0elo1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [h8058, hc24, hlam, hphi, ht0b, ht45, ht5b, p9370_1, u0elo1]
                                    · have p9370_0 := h9370c.1
                                      have p9370_1 := h9370c.2.1
                                      have p9370_2 := h9370c.2.2.1
                                      have p9370_3 := h9370c.2.2.2
                                      linarith only [hlam, p9370_0]
                                  · linarith only [h8881, h9369, hlam]
                                · linarith only [h8059, h9368, hlam]
                            · linarith only [h8056, h9365, hlam]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [h9003, hlam, p9304_1]
                        · have p9304_0 := h9304c.1
                          have p9304_1 := h9304c.2.1
                          have p9304_2 := h9304c.2.2.1
                          have p9304_3 := h9304c.2.2.2
                          linarith only [hlam, p9304_0]
                      · linarith only [h4610, h8057, h8059, h9003, h9303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h6681, h9003, h9111, hlam]
        · linarith only [h0, h8058, h9006, hlam]
      · linarith only [h0, h8057, h9005, hlam]
    · linarith only [h0, h8056, h9004, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9477 | h9477
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9478 | h9478
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9479 | h9479
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9480 | h9480
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9481 | h9481
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9482 | h9482
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9483 | h9483
                · linarith only [h4610, h8056, h8059, h9483, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9485 | h9485
                  · linarith only [h8056, h8881, h9485, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9487 | h9487
                    · linarith only [h8057, h9003, h9487, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9489 | h9489
                      · linarith only [h6681, h9003, h9477, h9480, h9489, hc01, hc12, hlam, hphi]
                      · linarith only [h4610, h8059, h9477, h9480, h9482, h9489, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9492 | h9492
                · linarith only [h8056, h8059, h9492, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9494 | h9494
                  · linarith only [h8056, h8881, h9494, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9496 | h9496
                    · linarith only [h6681, h8057, h9482, h9496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9498 | h9498
                      · linarith only [h9480, h9482, h9498, hlam]
                      · rcases h0bigk with h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c | h9500c
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h0, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h4610, hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h6681, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h7494, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          rcases p9500_3 (m.d 0 1) (by simp) with h9506 | h9506
                          · linarith only [h0, h9506, hlam]
                          · rcases p9500_3 (m.d 0 2) (by simp) with h9508 | h9508
                            · rcases p9500_3 (m.d 0 3) (by simp) with h9509 | h9509
                              · linarith only [h8056, h9509, hlam]
                              · linarith only [h4610, h9509, hlam]
                            · linarith only [h0, h9508, hlam]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          rcases p9500_3 (m.d 0 1) (by simp) with h9514 | h9514
                          · linarith only [h0, h9514, hlam]
                          · rcases p9500_3 (m.d 0 2) (by simp) with h9516 | h9516
                            · rcases p9500_3 (m.d 0 3) (by simp) with h9517 | h9517
                              · linarith only [h8056, h9517, hlam]
                              · rcases p9500_3 (m.d 0 4) (by simp) with h9519 | h9519
                                · linarith only [h8057, h9519, hlam]
                                · linarith only [h8059, h9519, hlam]
                            · linarith only [h8056, h9516, hlam]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          rcases p9500_3 (m.d 0 1) (by simp) with h9523 | h9523
                          · linarith only [h0, h9523, hlam]
                          · rcases p9500_3 (m.d 0 2) (by simp) with h9525 | h9525
                            · rcases p9500_3 (m.d 0 3) (by simp) with h9526 | h9526
                              · linarith only [h8056, h9526, hlam]
                              · rcases p9500_3 (m.d 0 4) (by simp) with h9528 | h9528
                                · linarith only [h8057, h9528, hlam]
                                · rcases p9500_3 (m.d 0 5) (by simp) with h9530 | h9530
                                  · linarith only [h8058, h9530, hlam]
                                  · linarith only [h9003, h9530, hlam]
                            · linarith only [h8057, h9525, hlam]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          rcases p9500_3 (m.d 0 1) (by simp) with h9534 | h9534
                          · linarith only [h0, h9534, hlam]
                          · rcases p9500_3 (m.d 0 2) (by simp) with h9536 | h9536
                            · rcases p9500_3 (m.d 0 3) (by simp) with h9537 | h9537
                              · linarith only [h8056, h9537, hlam]
                              · rcases p9500_3 (m.d 0 4) (by simp) with h9539 | h9539
                                · linarith only [h8057, h9539, hlam]
                                · rcases p9500_3 (m.d 0 5) (by simp) with h9541 | h9541
                                  · linarith only [h8058, h9541, hlam]
                                  · rcases h2bigk with h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c | h9543c
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h0, hlam, p9543_1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9546 | h9546
                                      · rcases p9543_3 (m.d 1 2) (by simp) with h9547 | h9547
                                        · rcases p9543_3 (m.d 2 3) (by simp) with h9548 | h9548
                                          · linarith only [h9548, hlam, p9543_0]
                                          · rcases p9543_3 (m.d 2 4) (by simp) with h9550 | h9550
                                            · linarith only [h8057, h9550, hlam]
                                            · linarith only [h9492, h9550, hlam]
                                        · linarith only [h9477, h9547, hlam]
                                      · linarith only [h9546, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9555 | h9555
                                      · rcases p9543_3 (m.d 1 2) (by simp) with h9556 | h9556
                                        · rcases p9543_3 (m.d 2 3) (by simp) with h9557 | h9557
                                          · linarith only [h8056, h9557, hlam]
                                          · rcases p9543_3 (m.d 2 4) (by simp) with h9559 | h9559
                                            · linarith only [h9559, hlam, p9543_0]
                                            · rcases p9543_3 (m.d 2 5) (by simp) with h9561 | h9561
                                              · linarith only [h8058, h9561, hlam]
                                              · linarith only [h9496, h9561, hlam]
                                        · linarith only [h9478, h9556, hlam]
                                      · linarith only [h9555, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9566 | h9566
                                      · rcases p9543_3 (m.d 1 2) (by simp) with h9567 | h9567
                                        · rcases p9543_3 (m.d 2 3) (by simp) with h9568 | h9568
                                          · linarith only [h8056, h9568, hlam]
                                          · rcases p9543_3 (m.d 2 4) (by simp) with h9570 | h9570
                                            · linarith only [h8057, h9570, hlam]
                                            · rcases p9543_3 (m.d 2 5) (by simp) with h9572 | h9572
                                              · linarith only [h9572, hlam, p9543_0]
                                              · rcases h3bigk with h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c | h9574c
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, hlam, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h8059, h9003, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9500_1, p9574_1, u0elo1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h8059, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h8881, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  rcases p9574_3 (m.d 0 3) (by simp) with h9580 | h9580
                                                  · linarith only [h4610, h9580, hlam]
                                                  · rcases p9574_3 (m.d 1 3) (by simp) with h9582 | h9582
                                                    · rcases p9574_3 (m.d 2 3) (by simp) with h9583 | h9583
                                                      · linarith only [h9477, h9583, hlam]
                                                      · rcases p9574_3 (m.d 3 4) (by simp) with h9585 | h9585
                                                        · linarith only [h9480, h9585, hlam]
                                                        · linarith only [h8059, h9585, hlam]
                                                    · linarith only [h4610, h9582, hlam]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  rcases p9574_3 (m.d 0 3) (by simp) with h9590 | h9590
                                                  · linarith only [h4610, h9590, hlam]
                                                  · linarith only [h8056, h9590, hlam]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, h8059, h9477, hc01, hc12, hlam, hphi, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, h8881, h9477, hc01, hc12, hlam, hphi, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h8056, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9477, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9492, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9494, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, h9477, h9480, hc01, hc12, hlam, hphi, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9480, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9480, h9482, hc23, hc45, hlam, hphi, ht34, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9498, hlam, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, h9477, h9481, hc01, hc12, hlam, hphi, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h9481, hlam, p9574_0]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  rcases p9574_3 (m.d 0 3) (by simp) with h9607 | h9607
                                                  · linarith only [h8881, h9607, hlam]
                                                  · linarith only [h8056, h9607, hlam]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [h4610, h8059, h9477, h9481, hc01, hc12, hlam, hphi, p9574_1]
                                                · have p9574_0 := h9574c.1
                                                  have p9574_1 := h9574c.2.1
                                                  have p9574_2 := h9574c.2.2.1
                                                  have p9574_3 := h9574c.2.2.2
                                                  linarith only [hlam, p9574_0]
                                        · linarith only [h9479, h9567, hlam]
                                      · linarith only [h9566, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9003, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9500_1, p9543_1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9616 | h9616
                                      · linarith only [h0, h9616, hlam]
                                      · linarith only [h8056, h9616, hlam]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9619 | h9619
                                      · linarith only [h0, h9619, hlam]
                                      · linarith only [h8057, h9619, hlam]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      rcases p9543_3 (m.d 0 2) (by simp) with h9622 | h9622
                                      · linarith only [h0, h9622, hlam]
                                      · linarith only [h8058, h9622, hlam]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8056, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9477, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9492, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9494, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8057, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9478, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9543_1, u0elo1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9496, hlam, p9543_1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8058, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h9479, hlam, p9543_0]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9500_1, p9543_1, u0elo1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [h8058, hc24, hlam, hphi, ht0b, ht45, ht5b, p9500_1, p9543_1, u0elo1]
                                    · have p9543_0 := h9543c.1
                                      have p9543_1 := h9543c.2.1
                                      have p9543_2 := h9543c.2.2.1
                                      have p9543_3 := h9543c.2.2.2
                                      linarith only [hlam, p9543_0]
                            · linarith only [h8058, h9536, hlam]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8059, hc01, hc34, hlam, hphi, ht12, ht23, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8056, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8059, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8881, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h6681, h9482, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8057, hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h6681, h9482, hc03, hc45, hlam, hphi, ht34, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h9003, hlam, p9500_0]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8881, h9477, h9481, hc01, hc12, hlam, hphi, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h8058, hlam, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h4610, h8881, h9477, h9481, hc01, hc12, hlam, hphi, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [h6681, h8881, h9477, h9481, hc01, hc12, hlam, hphi, p9500_1]
                        · have p9500_0 := h9500c.1
                          have p9500_1 := h9500c.2.1
                          have p9500_2 := h9500c.2.2.1
                          have p9500_3 := h9500c.2.2.2
                          linarith only [hlam, p9500_0]
            · linarith only [h4610, h8059, h9480, h9481, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9657 | h9657
            · linarith only [h4610, h8881, h9480, h9657, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9659 | h9659
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9660 | h9660
                · linarith only [h8056, h8059, h9660, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9662 | h9662
                  · linarith only [h4610, h9657, h9662, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9664 | h9664
                    · linarith only [h8057, h9003, h9664, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9666 | h9666
                      · rcases h0bigk with h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c | h9667c
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h0, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h4610, hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h6681, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h7494, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          rcases p9667_3 (m.d 0 1) (by simp) with h9673 | h9673
                          · linarith only [h0, h9673, hlam]
                          · rcases p9667_3 (m.d 0 2) (by simp) with h9675 | h9675
                            · rcases p9667_3 (m.d 0 3) (by simp) with h9676 | h9676
                              · linarith only [h8056, h9676, hlam]
                              · linarith only [h4610, h9676, hlam]
                            · linarith only [h0, h9675, hlam]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          rcases p9667_3 (m.d 0 1) (by simp) with h9681 | h9681
                          · linarith only [h0, h9681, hlam]
                          · rcases p9667_3 (m.d 0 2) (by simp) with h9683 | h9683
                            · rcases p9667_3 (m.d 0 3) (by simp) with h9684 | h9684
                              · linarith only [h8056, h9684, hlam]
                              · rcases p9667_3 (m.d 0 4) (by simp) with h9686 | h9686
                                · linarith only [h8057, h9686, hlam]
                                · linarith only [h8059, h9686, hlam]
                            · linarith only [h8056, h9683, hlam]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          rcases p9667_3 (m.d 0 1) (by simp) with h9690 | h9690
                          · linarith only [h0, h9690, hlam]
                          · rcases p9667_3 (m.d 0 2) (by simp) with h9692 | h9692
                            · rcases p9667_3 (m.d 0 3) (by simp) with h9693 | h9693
                              · linarith only [h8056, h9693, hlam]
                              · rcases p9667_3 (m.d 0 4) (by simp) with h9695 | h9695
                                · linarith only [h8057, h9695, hlam]
                                · rcases p9667_3 (m.d 0 5) (by simp) with h9697 | h9697
                                  · linarith only [h8058, h9697, hlam]
                                  · linarith only [h9003, h9697, hlam]
                            · linarith only [h8057, h9692, hlam]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          rcases p9667_3 (m.d 0 1) (by simp) with h9701 | h9701
                          · linarith only [h0, h9701, hlam]
                          · rcases p9667_3 (m.d 0 2) (by simp) with h9703 | h9703
                            · rcases p9667_3 (m.d 0 3) (by simp) with h9704 | h9704
                              · linarith only [h8056, h9704, hlam]
                              · rcases p9667_3 (m.d 0 4) (by simp) with h9706 | h9706
                                · linarith only [h8057, h9706, hlam]
                                · rcases p9667_3 (m.d 0 5) (by simp) with h9708 | h9708
                                  · linarith only [h8058, h9708, hlam]
                                  · rcases h2bigk with h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c | h9710c
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h0, hlam, p9710_1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9713 | h9713
                                      · rcases p9710_3 (m.d 1 2) (by simp) with h9714 | h9714
                                        · rcases p9710_3 (m.d 2 3) (by simp) with h9715 | h9715
                                          · linarith only [h9715, hlam, p9710_0]
                                          · rcases p9710_3 (m.d 2 4) (by simp) with h9717 | h9717
                                            · linarith only [h8057, h9717, hlam]
                                            · linarith only [h9660, h9717, hlam]
                                        · linarith only [h9477, h9714, hlam]
                                      · linarith only [h9713, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9722 | h9722
                                      · rcases p9710_3 (m.d 1 2) (by simp) with h9723 | h9723
                                        · rcases p9710_3 (m.d 2 3) (by simp) with h9724 | h9724
                                          · linarith only [h8056, h9724, hlam]
                                          · rcases p9710_3 (m.d 2 4) (by simp) with h9726 | h9726
                                            · linarith only [h9726, hlam, p9710_0]
                                            · rcases p9710_3 (m.d 2 5) (by simp) with h9728 | h9728
                                              · linarith only [h8058, h9728, hlam]
                                              · linarith only [h9664, h9728, hlam]
                                        · linarith only [h9478, h9723, hlam]
                                      · linarith only [h9722, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9733 | h9733
                                      · rcases p9710_3 (m.d 1 2) (by simp) with h9734 | h9734
                                        · rcases p9710_3 (m.d 2 3) (by simp) with h9735 | h9735
                                          · linarith only [h8056, h9735, hlam]
                                          · rcases p9710_3 (m.d 2 4) (by simp) with h9737 | h9737
                                            · linarith only [h8057, h9737, hlam]
                                            · rcases p9710_3 (m.d 2 5) (by simp) with h9739 | h9739
                                              · linarith only [h9739, hlam, p9710_0]
                                              · rcases h3bigk with h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h4610, hlam, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h8059, h9003, h9659, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h8059, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h8881, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9657, hc03, hc35, hlam, hphi, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9657, hc23, hc35, hlam, hphi, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9480, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9657, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h8056, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9477, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9660, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9662, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  rcases p9741_3 (m.d 0 3) (by simp) with h9757 | h9757
                                                  · linarith only [h9757, hlam, p9741_0]
                                                  · rcases p9741_3 (m.d 1 3) (by simp) with h9759 | h9759
                                                    · linarith only [h9480, h9759, hlam]
                                                    · linarith only [h4610, h9759, hlam]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h4610, hc01, hc34, hlam, hphi, ht12, ht23, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  rcases p9741_3 (m.d 0 3) (by simp) with h9763 | h9763
                                                  · linarith only [h8059, h9763, hlam]
                                                  · linarith only [h8056, h9763, hlam]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h4610, h8881, hc01, hc34, hlam, hphi, ht12, ht23, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  rcases p9741_3 (m.d 0 3) (by simp) with h9768 | h9768
                                                  · linarith only [h9768, hlam, p9741_0]
                                                  · rcases p9741_3 (m.d 1 3) (by simp) with h9770 | h9770
                                                    · linarith only [h9657, h9770, hlam]
                                                    · linarith only [h4610, h9770, hlam]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h4610, hc01, hc35, hlam, hphi, ht12, ht23, p9741_1]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  rcases p9741_3 (m.d 0 3) (by simp) with h9774 | h9774
                                                  · linarith only [h8881, h9774, hlam]
                                                  · linarith only [h8056, h9774, hlam]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [h9666, hlam, p9741_0]
                                                · have p9741_0 := h9741c.1
                                                  have p9741_1 := h9741c.2.1
                                                  have p9741_2 := h9741c.2.2.1
                                                  have p9741_3 := h9741c.2.2.2
                                                  linarith only [hlam, p9741_0]
                                        · linarith only [h9479, h9734, hlam]
                                      · linarith only [h9733, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h4610, h8059, h9003, hc01, hc12, hlam, hphi, p9667_1, p9710_1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9783 | h9783
                                      · linarith only [h0, h9783, hlam]
                                      · linarith only [h8056, h9783, hlam]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9786 | h9786
                                      · linarith only [h0, h9786, hlam]
                                      · linarith only [h8057, h9786, hlam]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      rcases p9710_3 (m.d 0 2) (by simp) with h9789 | h9789
                                      · linarith only [h0, h9789, hlam]
                                      · linarith only [h8058, h9789, hlam]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8056, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9477, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9660, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9662, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8057, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9478, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8057, h9003, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9667_1, p9710_1, u0elo1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9664, hlam, p9710_1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8058, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h9479, hlam, p9710_0]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8058, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9667_1, p9710_1, u0elo1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [h8058, hc24, hlam, hphi, ht0b, ht45, ht5b, p9667_1, p9710_1, u0elo1]
                                    · have p9710_0 := h9710c.1
                                      have p9710_1 := h9710c.2.1
                                      have p9710_2 := h9710c.2.2.1
                                      have p9710_3 := h9710c.2.2.2
                                      linarith only [hlam, p9710_0]
                            · linarith only [h8058, h9703, hlam]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8059, hc01, hc34, hlam, hphi, ht12, ht23, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8056, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8059, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8881, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h9003, h9480, h9659, hc01, hc34, hlam, hphi, ht12, ht23, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8057, hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h9003, h9480, h9659, hc03, hc34, hlam, hphi, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h9003, hlam, p9667_0]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h9003, h9480, h9659, hc01, hc34, hlam, hphi, ht12, ht23, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h8058, hlam, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h4610, h9003, h9480, h9659, hc01, hc34, hlam, hphi, ht12, ht23, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [h6681, h9003, h9480, h9659, hc01, hc34, hlam, hphi, ht12, ht23, p9667_1]
                        · have p9667_0 := h9667c.1
                          have p9667_1 := h9667c.2.1
                          have p9667_2 := h9667c.2.2.1
                          have p9667_3 := h9667c.2.2.2
                          linarith only [hlam, p9667_0]
                      · linarith only [h9480, h9659, h9666, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9824 | h9824
                · linarith only [h8056, h8059, h9824, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9826 | h9826
                  · linarith only [h4610, h8056, h8881, h9826, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9828 | h9828
                    · linarith only [h4610, h8057, h9480, h9659, h9828, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9830 | h9830
                      · linarith only [h4610, h9480, h9659, h9830, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h4610, h9480, h9830, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h8058, h9479, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h8057, h9478, hlam]
    · linarith only [h0, h8056, h9477, hlam]

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8059 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 5 (by decide) (by decide) with h8881 | h8881
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058 h8059 h8881
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058 h8059 h8881

set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 4 (by decide) (by decide) with h8059 | h8059
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058 h8059
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg4610 hg6681 hg7494 h8056 h8057 h8058 h8059

end R2N4
