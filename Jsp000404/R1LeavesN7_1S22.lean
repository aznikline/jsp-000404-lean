import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7824 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7825 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h8021 | h8021
  · linarith only [h0, h4, h7821, h8021, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8023 | h8023
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8024 | h8024
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8025 | h8025
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8026 | h8026
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8027 | h8027
            · linarith only [h2, h7825, h8027, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8029 | h8029
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8030 | h8030
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8031 | h8031
                  · linarith only [h0, h4, h7825, h8023, h8031, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8033 | h8033
                    · linarith only [h2, h7825, h8023, h8029, h8033, hlam]
                    · rcases h0bigk with h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c | h8035c
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8037 | h8037
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8038 | h8038
                          · linarith only [h0, h8038, hlam]
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8040 | h8040
                            · linarith only [h1, h8040, hlam]
                            · linarith only [h4, h8040, hlam]
                        · linarith only [h0, h8037, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8044 | h8044
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8045 | h8045
                          · linarith only [h0, h8045, hlam]
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8047 | h8047
                            · linarith only [h1, h8047, hlam]
                            · rcases p8035_3 (m.d 0 4) (by simp) with h8049 | h8049
                              · linarith only [h2, h8049, hlam]
                              · rcases p8035_3 (m.d 0 5) (by simp) with h8051 | h8051
                                · linarith only [h3, h8051, hlam]
                                · rcases h2bigk with h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c | h8053c
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h4, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h4, h8031, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h0, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8021, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h0, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h0, h4, h8031, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    rcases p8053_3 (m.d 0 2) (by simp) with h8064 | h8064
                                    · linarith only [h8064, hlam, p8053_0]
                                    · rcases p8053_3 (m.d 1 2) (by simp) with h8066 | h8066
                                      · linarith only [h8021, h8066, hlam]
                                      · rcases p8053_3 (m.d 2 3) (by simp) with h8068 | h8068
                                        · rcases p8053_3 (m.d 2 4) (by simp) with h8069 | h8069
                                          · linarith only [h8029, h8069, hlam]
                                          · rcases p8053_3 (m.d 2 5) (by simp) with h8071 | h8071
                                            · linarith only [h8030, h8071, hlam]
                                            · rcases h3bigk with h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c | h8073c
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8021, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8035_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h4, hlam, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8033, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h1, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8021, hlam, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h1, h8033, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                rcases p8073_3 (m.d 0 3) (by simp) with h8084 | h8084
                                                · linarith only [h4, h8084, hlam]
                                                · rcases p8073_3 (m.d 1 3) (by simp) with h8086 | h8086
                                                  · linarith only [h8021, h8086, hlam]
                                                  · rcases p8073_3 (m.d 2 3) (by simp) with h8088 | h8088
                                                    · rcases p8073_3 (m.d 3 4) (by simp) with h8089 | h8089
                                                      · linarith only [h8029, h8089, hlam]
                                                      · rcases p8073_3 (m.d 3 5) (by simp) with h8091 | h8091
                                                        · linarith only [h8030, h8091, hlam]
                                                        · rcases h5bigk with h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c | h8093c
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h7822, h8023, h8027, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8053_1, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h4, h7822, h8029, h8031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8073_1, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8073_1, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h7825, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h3, hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h3, h8029, h8031, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h3, h7825, h8033, hc34, hc45, hlam, hphi, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8027, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h7822, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8024, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8073_1, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8031, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h7824, hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8026, hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8030, hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [hlam, p8093_0]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8033, hlam, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h7824, h8033, hc34, hc45, hlam, hphi, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8026, h8033, hc34, hc45, hlam, hphi, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8030, h8033, hc34, hc45, hlam, hphi, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [h8033, hc34, hc45, hlam, hphi, p8093_1]
                                                          · have p8093_0 := h8093c.1
                                                            have p8093_1 := h8093c.2.1
                                                            have p8093_2 := h8093c.2.2.1
                                                            have p8093_3 := h8093c.2.2.2
                                                            linarith only [hlam, p8093_0]
                                                    · linarith only [h4, h8088, hlam]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                rcases p8073_3 (m.d 0 3) (by simp) with h8120 | h8120
                                                · linarith only [h4, h8120, hlam]
                                                · linarith only [h1, h8120, hlam]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h0, h8024, h8030, h8033, hlam, p8053_1, p8073_2]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h0, h8024, h8030, hlam, p8053_1, p8073_2]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h7823, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8025, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8029, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8033, hlam, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h7824, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8026, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h8030, hlam, p8073_0]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [h0, h8024, h8030, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8053_1, p8073_1]
                                              · have p8073_0 := h8073c.1
                                                have p8073_1 := h8073c.2.1
                                                have p8073_2 := h8073c.2.2.1
                                                have p8073_3 := h8073c.2.2.2
                                                linarith only [hlam, p8073_0]
                                        · linarith only [h8068, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    rcases p8053_3 (m.d 0 2) (by simp) with h8137 | h8137
                                    · linarith only [h4, h8137, hlam]
                                    · linarith only [h0, h8137, hlam]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    rcases p8053_3 (m.d 0 2) (by simp) with h8141 | h8141
                                    · linarith only [h4, h8141, hlam]
                                    · linarith only [h7821, h8141, hlam]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    rcases p8053_3 (m.d 0 2) (by simp) with h8144 | h8144
                                    · linarith only [h4, h8144, hlam]
                                    · linarith only [h7822, h8144, hlam]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h7821, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8023, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8029, hlam, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8031, hlam, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h7822, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8024, hlam, p8053_0]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h8030, hlam, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [h0, h4, h8024, h8029, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8053_1]
                                  · have p8053_0 := h8053c.1
                                    have p8053_1 := h8053c.2.1
                                    have p8053_2 := h8053c.2.2.1
                                    have p8053_3 := h8053c.2.2.2
                                    linarith only [hlam, p8053_0]
                        · linarith only [h1, h8044, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8158 | h8158
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8159 | h8159
                          · linarith only [h0, h8159, hlam]
                          · linarith only [h7821, h8159, hlam]
                        · linarith only [h2, h8158, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8163 | h8163
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8164 | h8164
                          · linarith only [h0, h8164, hlam]
                          · linarith only [h7822, h8164, hlam]
                        · linarith only [h3, h8163, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h0, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h4, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8171 | h8171
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8172 | h8172
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8173 | h8173
                            · rcases p8035_3 (m.d 0 4) (by simp) with h8174 | h8174
                              · linarith only [h7821, h8174, hlam]
                              · rcases p8035_3 (m.d 0 5) (by simp) with h8176 | h8176
                                · linarith only [h7822, h8176, hlam]
                                · linarith only [h7825, h8176, hlam]
                            · linarith only [h7823, h8173, hlam]
                          · linarith only [h7821, h8172, hlam]
                        · linarith only [h2, h8171, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8182 | h8182
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8183 | h8183
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8184 | h8184
                            · rcases p8035_3 (m.d 0 4) (by simp) with h8185 | h8185
                              · linarith only [h7821, h8185, hlam]
                              · rcases p8035_3 (m.d 0 5) (by simp) with h8187 | h8187
                                · linarith only [h7822, h8187, hlam]
                                · rcases h2bigk with h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c | h8189c
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h4, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    rcases p8189_3 (m.d 0 2) (by simp) with h8193 | h8193
                                    · rcases p8189_3 (m.d 1 2) (by simp) with h8194 | h8194
                                      · linarith only [h0, h8194, hlam]
                                      · linarith only [h8023, h8194, hlam]
                                    · linarith only [h8193, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    rcases p8189_3 (m.d 0 2) (by simp) with h8198 | h8198
                                    · rcases p8189_3 (m.d 1 2) (by simp) with h8199 | h8199
                                      · linarith only [h0, h8199, hlam]
                                      · linarith only [h8024, h8199, hlam]
                                    · linarith only [h8198, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h0, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8021, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    rcases p8189_3 (m.d 0 2) (by simp) with h8206 | h8206
                                    · rcases p8189_3 (m.d 1 2) (by simp) with h8207 | h8207
                                      · rcases p8189_3 (m.d 2 3) (by simp) with h8208 | h8208
                                        · rcases p8189_3 (m.d 2 4) (by simp) with h8209 | h8209
                                          · linarith only [h8209, hlam, p8189_0]
                                          · rcases p8189_3 (m.d 2 5) (by simp) with h8211 | h8211
                                            · linarith only [h8024, h8211, hlam]
                                            · linarith only [h8031, h8211, hlam]
                                        · linarith only [h8029, h8208, hlam]
                                      · linarith only [h8207, hlam, p8189_0]
                                    · linarith only [h7821, h8206, hlam]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    rcases p8189_3 (m.d 0 2) (by simp) with h8217 | h8217
                                    · rcases p8189_3 (m.d 1 2) (by simp) with h8218 | h8218
                                      · rcases p8189_3 (m.d 2 3) (by simp) with h8219 | h8219
                                        · rcases p8189_3 (m.d 2 4) (by simp) with h8220 | h8220
                                          · linarith only [h8023, h8220, hlam]
                                          · rcases p8189_3 (m.d 2 5) (by simp) with h8222 | h8222
                                            · linarith only [h8222, hlam, p8189_0]
                                            · rcases h3bigk with h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8021, hc03, hc25, hlam, hphi, ht0b, ht5b, p8189_1, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h4, hlam, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                rcases p8224_3 (m.d 0 3) (by simp) with h8228 | h8228
                                                · rcases p8224_3 (m.d 1 3) (by simp) with h8229 | h8229
                                                  · linarith only [h1, h8229, hlam]
                                                  · linarith only [h8025, h8229, hlam]
                                                · linarith only [h8228, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                rcases p8224_3 (m.d 0 3) (by simp) with h8233 | h8233
                                                · rcases p8224_3 (m.d 1 3) (by simp) with h8234 | h8234
                                                  · linarith only [h1, h8234, hlam]
                                                  · linarith only [h8026, h8234, hlam]
                                                · linarith only [h8233, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h1, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8021, hlam, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                rcases p8224_3 (m.d 0 3) (by simp) with h8241 | h8241
                                                · rcases p8224_3 (m.d 1 3) (by simp) with h8242 | h8242
                                                  · rcases p8224_3 (m.d 2 3) (by simp) with h8243 | h8243
                                                    · rcases p8224_3 (m.d 3 4) (by simp) with h8244 | h8244
                                                      · linarith only [h8244, hlam, p8224_0]
                                                      · rcases p8224_3 (m.d 3 5) (by simp) with h8246 | h8246
                                                        · linarith only [h8026, h8246, hlam]
                                                        · linarith only [h8033, h8246, hlam]
                                                    · linarith only [h8029, h8243, hlam]
                                                  · linarith only [h8242, hlam, p8224_0]
                                                · linarith only [h7823, h8241, hlam]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                rcases p8224_3 (m.d 0 3) (by simp) with h8252 | h8252
                                                · rcases p8224_3 (m.d 1 3) (by simp) with h8253 | h8253
                                                  · rcases p8224_3 (m.d 2 3) (by simp) with h8254 | h8254
                                                    · rcases p8224_3 (m.d 3 4) (by simp) with h8255 | h8255
                                                      · linarith only [h8025, h8255, hlam]
                                                      · rcases p8224_3 (m.d 3 5) (by simp) with h8257 | h8257
                                                        · linarith only [h8257, hlam, p8224_0]
                                                        · rcases h5bigk with h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h4, h8029, h8031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h4, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h7825, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h3, hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h3, h8029, h8031, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h3, h4, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8027, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h7822, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8024, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8033, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8189_1, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8031, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h7824, hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8026, hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8030, hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [hlam, p8259_0]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8033, hlam, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h7824, h8033, hc34, hc45, hlam, hphi, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8026, h8033, hc34, hc45, hlam, hphi, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8030, h8033, hc34, hc45, hlam, hphi, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [h8033, hc34, hc45, hlam, hphi, p8259_1]
                                                          · have p8259_0 := h8259c.1
                                                            have p8259_1 := h8259c.2.1
                                                            have p8259_2 := h8259c.2.2.1
                                                            have p8259_3 := h8259c.2.2.2
                                                            linarith only [hlam, p8259_0]
                                                    · linarith only [h8030, h8254, hlam]
                                                  · linarith only [h8253, hlam, p8224_0]
                                                · linarith only [h7824, h8252, hlam]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h2, h4, h7825, h8023, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8021, h8030, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8189_1, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h2, h4, h7825, h8023, h8029, hlam, p8035_1, p8224_2]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h0, h4, h8030, hlam, p8189_1, p8224_2]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h7823, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8025, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8029, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8033, hlam, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h7824, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8026, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h8030, hlam, p8224_0]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [h3, h8024, h8030, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8224_1]
                                              · have p8224_0 := h8224c.1
                                                have p8224_1 := h8224c.2.1
                                                have p8224_2 := h8224c.2.2.1
                                                have p8224_3 := h8224c.2.2.2
                                                linarith only [hlam, p8224_0]
                                        · linarith only [h8030, h8219, hlam]
                                      · linarith only [h8218, hlam, p8189_0]
                                    · linarith only [h7822, h8217, hlam]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    rcases p8189_3 (m.d 0 2) (by simp) with h8307 | h8307
                                    · linarith only [h4, h8307, hlam]
                                    · linarith only [h0, h8307, hlam]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h2, h4, h7825, h8023, hlam, p8035_1, p8189_2]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h4, h7822, hlam, p8035_1, p8189_2]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h7821, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8023, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8029, hlam, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8031, hlam, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h7822, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8024, hlam, p8189_0]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h8030, hlam, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [h3, h8024, h8029, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8189_1]
                                  · have p8189_0 := h8189c.1
                                    have p8189_1 := h8189c.2.1
                                    have p8189_2 := h8189c.2.2.1
                                    have p8189_3 := h8189c.2.2.2
                                    linarith only [hlam, p8189_0]
                            · linarith only [h7824, h8184, hlam]
                          · linarith only [h7822, h8183, hlam]
                        · linarith only [h3, h8182, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h1, hlam, p8035_1]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8327 | h8327
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8328 | h8328
                          · linarith only [h4, h8328, hlam]
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8330 | h8330
                            · rcases p8035_3 (m.d 0 4) (by simp) with h8331 | h8331
                              · linarith only [h7823, h8331, hlam]
                              · rcases p8035_3 (m.d 0 5) (by simp) with h8333 | h8333
                                · linarith only [h7824, h8333, hlam]
                                · rcases h2bigk with h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c | h8335c
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h4, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h4, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h0, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8021, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h0, h4, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h0, h4, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    rcases p8335_3 (m.d 0 2) (by simp) with h8346 | h8346
                                    · linarith only [h8346, hlam, p8335_0]
                                    · rcases p8335_3 (m.d 1 2) (by simp) with h8348 | h8348
                                      · linarith only [h8021, h8348, hlam]
                                      · rcases p8335_3 (m.d 2 3) (by simp) with h8350 | h8350
                                        · rcases p8335_3 (m.d 2 4) (by simp) with h8351 | h8351
                                          · linarith only [h8029, h8351, hlam]
                                          · rcases p8335_3 (m.d 2 5) (by simp) with h8353 | h8353
                                            · linarith only [h8030, h8353, hlam]
                                            · rcases h3bigk with h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c | h8355c
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                rcases p8355_3 (m.d 0 3) (by simp) with h8357 | h8357
                                                · rcases p8355_3 (m.d 1 3) (by simp) with h8358 | h8358
                                                  · linarith only [h1, h8358, hlam]
                                                  · rcases p8355_3 (m.d 2 3) (by simp) with h8360 | h8360
                                                    · rcases p8355_3 (m.d 3 4) (by simp) with h8361 | h8361
                                                      · linarith only [h7823, h8361, hlam]
                                                      · rcases p8355_3 (m.d 3 5) (by simp) with h8363 | h8363
                                                        · linarith only [h7824, h8363, hlam]
                                                        · rcases h5bigk with h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c | h8365c
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h4, h7822, h8023, h8027, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h4, h7822, h8030, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h7825, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h3, hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h3, h8030, h8033, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h3, h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8027, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h7822, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8024, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8031, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h7824, hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8026, hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8030, hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [hlam, p8365_0]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8033, hlam, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h7824, h8033, hc34, hc45, hlam, hphi, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8026, h8033, hc34, hc45, hlam, hphi, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8030, h8033, hc34, hc45, hlam, hphi, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [h8033, hc34, hc45, hlam, hphi, p8365_1]
                                                          · have p8365_0 := h8365c.1
                                                            have p8365_1 := h8365c.2.1
                                                            have p8365_2 := h8365c.2.2.1
                                                            have p8365_3 := h8365c.2.2.2
                                                            linarith only [hlam, p8365_0]
                                                    · linarith only [h8021, h8360, hlam]
                                                · linarith only [h1, h8357, hlam]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h4, hlam, p8355_1]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h7821, h8029, hlam, p8035_1, p8355_2]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h7822, h8030, hlam, p8035_1, p8355_2]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h1, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8021, hlam, p8355_1]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                rcases p8355_3 (m.d 0 3) (by simp) with h8399 | h8399
                                                · rcases p8355_3 (m.d 1 3) (by simp) with h8400 | h8400
                                                  · rcases p8355_3 (m.d 2 3) (by simp) with h8401 | h8401
                                                    · rcases p8355_3 (m.d 3 4) (by simp) with h8402 | h8402
                                                      · linarith only [h8402, hlam, p8355_0]
                                                      · rcases p8355_3 (m.d 3 5) (by simp) with h8404 | h8404
                                                        · linarith only [h8026, h8404, hlam]
                                                        · linarith only [h8033, h8404, hlam]
                                                    · linarith only [h8029, h8401, hlam]
                                                  · linarith only [h8400, hlam, p8355_0]
                                                · linarith only [h7823, h8399, hlam]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                rcases p8355_3 (m.d 0 3) (by simp) with h8410 | h8410
                                                · rcases p8355_3 (m.d 1 3) (by simp) with h8411 | h8411
                                                  · rcases p8355_3 (m.d 2 3) (by simp) with h8412 | h8412
                                                    · rcases p8355_3 (m.d 3 4) (by simp) with h8413 | h8413
                                                      · linarith only [h8025, h8413, hlam]
                                                      · rcases p8355_3 (m.d 3 5) (by simp) with h8415 | h8415
                                                        · linarith only [h8415, hlam, p8355_0]
                                                        · rcases h5bigk with h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h7822, h8023, h8027, h8029, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h4, h7822, h8030, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h7825, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h3, hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h3, h8030, h8033, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h3, h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8027, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h7822, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8024, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8031, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h7824, hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8026, hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8030, hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [hlam, p8417_0]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8033, hlam, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h7824, h8033, hc34, hc45, hlam, hphi, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8026, h8033, hc34, hc45, hlam, hphi, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8030, h8033, hc34, hc45, hlam, hphi, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [h8033, hc34, hc45, hlam, hphi, p8417_1]
                                                          · have p8417_0 := h8417c.1
                                                            have p8417_1 := h8417c.2.1
                                                            have p8417_2 := h8417c.2.2.1
                                                            have p8417_3 := h8417c.2.2.2
                                                            linarith only [hlam, p8417_0]
                                                    · linarith only [h8030, h8412, hlam]
                                                  · linarith only [h8411, hlam, p8355_0]
                                                · linarith only [h7824, h8410, hlam]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hc02, hc23, hlam, hphi, p8035_1, p8355_1]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                rcases p8355_3 (m.d 0 3) (by simp) with h8447 | h8447
                                                · linarith only [h4, h8447, hlam]
                                                · linarith only [h1, h8447, hlam]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h0, h8024, h8030, h8033, hlam, p8335_1, p8355_2]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h0, h4, h8024, h8030, hlam, p8035_1, p8355_2]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h7823, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8025, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8029, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8033, hlam, p8355_1]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h7824, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8026, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h8030, hlam, p8355_0]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [h0, h8024, h8030, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8035_1, p8355_1]
                                              · have p8355_0 := h8355c.1
                                                have p8355_1 := h8355c.2.1
                                                have p8355_2 := h8355c.2.2.1
                                                have p8355_3 := h8355c.2.2.2
                                                linarith only [hlam, p8355_0]
                                        · linarith only [h8350, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    rcases p8335_3 (m.d 0 2) (by simp) with h8464 | h8464
                                    · linarith only [h4, h8464, hlam]
                                    · linarith only [h0, h8464, hlam]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h4, h7821, hlam, p8035_1, p8335_2]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h0, h4, h8024, hlam, p8035_1, p8335_2]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h7821, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8023, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8029, hlam, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8031, hlam, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h7822, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8024, hlam, p8335_0]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h8030, hlam, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [h0, h4, h8024, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8335_1]
                                  · have p8335_0 := h8335c.1
                                    have p8335_1 := h8335c.2.1
                                    have p8335_2 := h8335c.2.2.1
                                    have p8335_3 := h8335c.2.2.2
                                    linarith only [hlam, p8335_0]
                            · linarith only [h4, h8330, hlam]
                        · linarith only [h0, h8327, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8483 | h8483
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8484 | h8484
                          · linarith only [h4, h8484, hlam]
                          · linarith only [h7821, h8484, hlam]
                        · linarith only [h2, h8483, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8488 | h8488
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8489 | h8489
                          · linarith only [h4, h8489, hlam]
                          · linarith only [h7822, h8489, hlam]
                        · linarith only [h3, h8488, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h2, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h7821, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h7823, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h7825, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h3, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h7822, hlam, p8035_1]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [h7824, hlam, p8035_0]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        rcases p8035_3 (m.d 0 1) (by simp) with h8501 | h8501
                        · rcases p8035_3 (m.d 0 2) (by simp) with h8502 | h8502
                          · rcases p8035_3 (m.d 0 3) (by simp) with h8503 | h8503
                            · rcases p8035_3 (m.d 0 4) (by simp) with h8504 | h8504
                              · linarith only [h7825, h8504, hlam]
                              · rcases p8035_3 (m.d 0 5) (by simp) with h8506 | h8506
                                · rcases h2bigk with h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c | h8507c
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h4, h8024, h8030, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h4, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8511 | h8511
                                    · rcases p8507_3 (m.d 1 2) (by simp) with h8512 | h8512
                                      · linarith only [h0, h8512, hlam]
                                      · linarith only [h8023, h8512, hlam]
                                    · linarith only [h8511, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8516 | h8516
                                    · rcases p8507_3 (m.d 1 2) (by simp) with h8517 | h8517
                                      · linarith only [h0, h8517, hlam]
                                      · linarith only [h8024, h8517, hlam]
                                    · linarith only [h8516, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h0, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8021, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8524 | h8524
                                    · rcases p8507_3 (m.d 1 2) (by simp) with h8525 | h8525
                                      · rcases p8507_3 (m.d 2 3) (by simp) with h8526 | h8526
                                        · rcases p8507_3 (m.d 2 4) (by simp) with h8527 | h8527
                                          · linarith only [h8527, hlam, p8507_0]
                                          · rcases p8507_3 (m.d 2 5) (by simp) with h8529 | h8529
                                            · linarith only [h8024, h8529, hlam]
                                            · linarith only [h8031, h8529, hlam]
                                        · linarith only [h8029, h8526, hlam]
                                      · linarith only [h8525, hlam, p8507_0]
                                    · linarith only [h7821, h8524, hlam]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8535 | h8535
                                    · rcases p8507_3 (m.d 1 2) (by simp) with h8536 | h8536
                                      · rcases p8507_3 (m.d 2 3) (by simp) with h8537 | h8537
                                        · rcases p8507_3 (m.d 2 4) (by simp) with h8538 | h8538
                                          · linarith only [h8023, h8538, hlam]
                                          · rcases p8507_3 (m.d 2 5) (by simp) with h8540 | h8540
                                            · linarith only [h8540, hlam, p8507_0]
                                            · rcases h3bigk with h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c | h8542c
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h4, h8021, h8029, h8031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8507_1, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h4, hlam, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                rcases p8542_3 (m.d 0 3) (by simp) with h8546 | h8546
                                                · rcases p8542_3 (m.d 1 3) (by simp) with h8547 | h8547
                                                  · linarith only [h1, h8547, hlam]
                                                  · linarith only [h8025, h8547, hlam]
                                                · linarith only [h8546, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                rcases p8542_3 (m.d 0 3) (by simp) with h8551 | h8551
                                                · rcases p8542_3 (m.d 1 3) (by simp) with h8552 | h8552
                                                  · linarith only [h1, h8552, hlam]
                                                  · linarith only [h8026, h8552, hlam]
                                                · linarith only [h8551, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h1, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8021, hlam, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                rcases p8542_3 (m.d 0 3) (by simp) with h8559 | h8559
                                                · rcases p8542_3 (m.d 1 3) (by simp) with h8560 | h8560
                                                  · rcases p8542_3 (m.d 2 3) (by simp) with h8561 | h8561
                                                    · rcases p8542_3 (m.d 3 4) (by simp) with h8562 | h8562
                                                      · linarith only [h8562, hlam, p8542_0]
                                                      · rcases p8542_3 (m.d 3 5) (by simp) with h8564 | h8564
                                                        · linarith only [h8026, h8564, hlam]
                                                        · linarith only [h8033, h8564, hlam]
                                                    · linarith only [h8029, h8561, hlam]
                                                  · linarith only [h8560, hlam, p8542_0]
                                                · linarith only [h7823, h8559, hlam]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                rcases p8542_3 (m.d 0 3) (by simp) with h8570 | h8570
                                                · rcases p8542_3 (m.d 1 3) (by simp) with h8571 | h8571
                                                  · rcases p8542_3 (m.d 2 3) (by simp) with h8572 | h8572
                                                    · rcases p8542_3 (m.d 3 4) (by simp) with h8573 | h8573
                                                      · linarith only [h8025, h8573, hlam]
                                                      · rcases p8542_3 (m.d 3 5) (by simp) with h8575 | h8575
                                                        · linarith only [h8575, hlam, p8542_0]
                                                        · rcases h5bigk with h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c | h8577c
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h4, h7822, h8023, h8027, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h4, h7822, h8029, h8031, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h7825, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h3, hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h3, h8029, h8031, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h0, h8024, h8033, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8027, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h7822, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8024, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h4, h7822, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8031, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h7824, hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8026, hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8030, hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hlam, p8577_0]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8033, hlam, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hc04, hc45, hlam, hphi, p8035_1, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8026, h8033, hc34, hc45, hlam, hphi, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8030, h8033, hc34, hc45, hlam, hphi, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [h8033, hc34, hc45, hlam, hphi, p8577_1]
                                                          · have p8577_0 := h8577c.1
                                                            have p8577_1 := h8577c.2.1
                                                            have p8577_2 := h8577c.2.2.1
                                                            have p8577_3 := h8577c.2.2.2
                                                            linarith only [hlam, p8577_0]
                                                    · linarith only [h8030, h8572, hlam]
                                                  · linarith only [h8571, hlam, p8542_0]
                                                · linarith only [h7824, h8570, hlam]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h2, h4, h7822, h8023, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8021, h8030, h8033, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8507_1, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h2, h4, h7822, h8023, h8029, hlam, p8035_1, p8542_2]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h0, h4, h8030, hlam, p8507_1, p8542_2]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h7823, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8025, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8029, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8033, hlam, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h7824, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8026, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h8030, hlam, p8542_0]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [h0, h8030, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8507_1, p8542_1]
                                              · have p8542_0 := h8542c.1
                                                have p8542_1 := h8542c.2.1
                                                have p8542_2 := h8542c.2.2.1
                                                have p8542_3 := h8542c.2.2.2
                                                linarith only [hlam, p8542_0]
                                        · linarith only [h8030, h8537, hlam]
                                      · linarith only [h8536, hlam, p8507_0]
                                    · linarith only [h7822, h8535, hlam]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h2, h7822, h8023, h8029, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8035_1, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8625 | h8625
                                    · linarith only [h4, h8625, hlam]
                                    · linarith only [h0, h8625, hlam]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h2, h4, h7822, h8023, hlam, p8035_1, p8507_2]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    rcases p8507_3 (m.d 0 2) (by simp) with h8630 | h8630
                                    · linarith only [h4, h8630, hlam]
                                    · linarith only [h7822, h8630, hlam]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h7821, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8023, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8029, hlam, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8031, hlam, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h7822, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8024, hlam, p8507_0]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h8030, hlam, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [h0, h8024, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p8507_1]
                                  · have p8507_0 := h8507c.1
                                    have p8507_1 := h8507c.2.1
                                    have p8507_2 := h8507c.2.2.1
                                    have p8507_3 := h8507c.2.2.2
                                    linarith only [hlam, p8507_0]
                                · linarith only [h7825, h8506, hlam]
                            · linarith only [h7823, h8503, hlam]
                          · linarith only [h7821, h8502, hlam]
                        · linarith only [h2, h8501, hlam]
                      · have p8035_0 := h8035c.1
                        have p8035_1 := h8035c.2.1
                        have p8035_2 := h8035c.2.2.1
                        have p8035_3 := h8035c.2.2.2
                        linarith only [hlam, p8035_0]
                · linarith only [h0, h4, h8024, h8026, h8030, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h4, h7823, h8029, hlam]
          · linarith only [h8021, h8024, h8026, hlam]
        · linarith only [h7823, h7825, h8021, h8023, h8025, hc24, hc45, hlam, hphi]
      · linarith only [h4, h7822, h8023, h8024, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
    · linarith only [h4, h7821, h8023, hc12, hc23, hlam, hphi]

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7824 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h7825 | h7825
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823 h7824 h7825
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823 h7824 h7825

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7824 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h4, h7822, h7824, hlam]

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h7824 | h7824
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823 h7824
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823 h7824

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  linarith only [h4, h7821, h7823, hlam]

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h7823 | h7823
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h7821 h7822 h7823

end R2N4
