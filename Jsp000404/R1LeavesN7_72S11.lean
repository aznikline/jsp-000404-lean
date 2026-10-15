import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_72S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_0_L_0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h499 | h499
  · rcases m.htr 0 2 4 (by decide) (by decide) with h500 | h500
    · rcases m.htr 0 2 5 (by decide) (by decide) with h501 | h501
      · rcases m.htr 0 3 4 (by decide) (by decide) with h502 | h502
        · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
          · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
            · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
              · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h509 | h509
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                        · rcases h2bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h507, h510, hc02, hc45, hlam, hphi, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, h507, h510, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            rcases p511_3 (m.d 0 2) (by simp) with h516 | h516
                            · rcases p511_3 (m.d 1 2) (by simp) with h517 | h517
                              · rcases p511_3 (m.d 2 3) (by simp) with h518 | h518
                                · linarith only [h499, h518, hlam]
                                · linarith only [h508, h518, hlam]
                              · linarith only [h505, h517, hlam]
                            · linarith only [h516, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h507, h510, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h507, h510, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            rcases p511_3 (m.d 0 2) (by simp) with h527 | h527
                            · linarith only [h0, h527, hlam]
                            · linarith only [h501, h527, hlam]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h499, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h503, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h499, h507, h510, hc02, hc45, hlam, hphi, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h499, h508, h510, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p511_1, u3elo0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h500, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h504, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h507, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h0, h500, h508, h510, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h501, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h505, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h508, hlam, p511_0]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [h509, hlam, p511_1]
                          · have p511_0 := h511c.1
                            have p511_1 := h511c.2.1
                            have p511_2 := h511c.2.2.1
                            have p511_3 := h511c.2.2.2
                            linarith only [hlam, p511_0]
                        · rcases h2bigk with h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c | h545c
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h0, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h0, h507, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h0, h509, h510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h0, h509, h510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h508, h509, h510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h509, h510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h509, h510, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h499, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h503, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h509, h510, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h499, h509, h510, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p545_1, u3elo0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h500, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h504, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h507, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h504, h509, h510, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h501, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h505, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h508, hlam, p545_0]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [h509, hlam, p545_1]
                          · have p545_0 := h545c.1
                            have p545_1 := h545c.2.1
                            have p545_2 := h545c.2.2.1
                            have p545_3 := h545c.2.2.2
                            linarith only [hlam, p545_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                        · linarith only [h502, h509, h571, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · rcases h2bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h0, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h0, h507, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p573_1]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            rcases p573_3 (m.d 0 2) (by simp) with h577 | h577
                            · rcases p573_3 (m.d 1 2) (by simp) with h578 | h578
                              · rcases p573_3 (m.d 2 3) (by simp) with h579 | h579
                                · linarith only [h499, h579, hlam]
                                · linarith only [h507, h579, hlam]
                              · linarith only [h504, h578, hlam]
                            · linarith only [h577, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            rcases p573_3 (m.d 0 2) (by simp) with h584 | h584
                            · rcases p573_3 (m.d 1 2) (by simp) with h585 | h585
                              · rcases p573_3 (m.d 2 3) (by simp) with h586 | h586
                                · linarith only [h499, h586, hlam]
                                · linarith only [h508, h586, hlam]
                              · linarith only [h505, h585, hlam]
                            · linarith only [h584, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p573_1]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h508, h571, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p573_1]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            rcases p573_3 (m.d 0 2) (by simp) with h594 | h594
                            · linarith only [h0, h594, hlam]
                            · linarith only [h500, h594, hlam]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            rcases p573_3 (m.d 0 2) (by simp) with h597 | h597
                            · linarith only [h0, h597, hlam]
                            · linarith only [h501, h597, hlam]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h499, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h503, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h503, h507, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p573_1, u3elo1]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h503, h508, h571, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p573_1, u3elo1]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h500, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h504, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h507, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h509, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h501, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h505, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h508, hlam, p573_0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [h501, h507, hc34, hlam, hphi, ht45, p573_1, u5elo0]
                          · have p573_0 := h573c.1
                            have p573_1 := h573c.2.1
                            have p573_2 := h573c.2.2.1
                            have p573_3 := h573c.2.2.2
                            linarith only [hlam, p573_0]
                    · linarith only [h507, h508, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h502, h507, hc23, hlam, hphi, u3elo0]
                · linarith only [h502, h506, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h501, h505, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h500, h504, hlam]
          · linarith only [h0, h503, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
          · rcases m.htr 1 2 4 (by decide) (by decide) with h622 | h622
            · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
              · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                · linarith only [h502, h624, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h626 | h626
                  · linarith only [h499, h624, h626, hc13, hlam, hphi, u3elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h628 | h628
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h629 | h629
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                        · rcases h2bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h0, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h628, h630, hc02, hc45, hlam, hphi, ht0b, ht5b, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h0, h626, h628, h630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            rcases p631_3 (m.d 0 2) (by simp) with h636 | h636
                            · rcases p631_3 (m.d 1 2) (by simp) with h637 | h637
                              · rcases p631_3 (m.d 2 3) (by simp) with h638 | h638
                                · linarith only [h499, h638, hlam]
                                · linarith only [h628, h638, hlam]
                              · linarith only [h623, h637, hlam]
                            · linarith only [h636, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h628, h630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h626, h628, h630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            rcases p631_3 (m.d 0 2) (by simp) with h647 | h647
                            · linarith only [h0, h647, hlam]
                            · linarith only [h501, h647, hlam]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h499, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h621, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h626, hlam, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h499, h502, h628, h630, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p631_1, u3elo3]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h500, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h622, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h500, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h500, h502, h628, h630, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p631_1, u3elo3]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h501, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h623, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h628, hlam, p631_0]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [h629, hlam, p631_1]
                          · have p631_0 := h631c.1
                            have p631_1 := h631c.2.1
                            have p631_2 := h631c.2.2.1
                            have p631_3 := h631c.2.2.2
                            linarith only [hlam, p631_0]
                        · linarith only [h499, h502, h628, h630, hc35, hlam, hphi, u5elo4]
                      · linarith only [h626, h628, h629, hc35, hlam, hphi, u5elo4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h667 | h667
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h668 | h668
                        · rcases h2bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h0, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            rcases p669_3 (m.d 0 2) (by simp) with h672 | h672
                            · rcases p669_3 (m.d 1 2) (by simp) with h673 | h673
                              · rcases p669_3 (m.d 2 3) (by simp) with h674 | h674
                                · linarith only [h674, hlam, p669_0]
                                · rcases p669_3 (m.d 2 4) (by simp) with h676 | h676
                                  · linarith only [h500, h676, hlam]
                                  · linarith only [h626, h676, hlam]
                              · linarith only [h621, h673, hlam]
                            · linarith only [h672, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h0, h667, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            rcases p669_3 (m.d 0 2) (by simp) with h682 | h682
                            · rcases p669_3 (m.d 1 2) (by simp) with h683 | h683
                              · rcases p669_3 (m.d 2 3) (by simp) with h684 | h684
                                · linarith only [h499, h684, hlam]
                                · rcases p669_3 (m.d 2 4) (by simp) with h686 | h686
                                  · linarith only [h500, h686, hlam]
                                  · linarith only [h667, h686, hlam]
                              · linarith only [h623, h683, hlam]
                            · linarith only [h682, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            rcases p669_3 (m.d 0 2) (by simp) with h693 | h693
                            · linarith only [h0, h693, hlam]
                            · linarith only [h499, h693, hlam]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h667, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            rcases p669_3 (m.d 0 2) (by simp) with h697 | h697
                            · linarith only [h0, h697, hlam]
                            · linarith only [h501, h697, hlam]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h499, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h621, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h626, hlam, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h628, hlam, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h500, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h622, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h500, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h500, h502, h628, hc23, hlam, hphi, p669_1, u3elo3]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h501, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h623, hlam, p669_0]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hc23, hlam, hphi, ht34, ht45, p669_1, u5elo2]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [h667, hlam, p669_1]
                          · have p669_0 := h669c.1
                            have p669_1 := h669c.2.1
                            have p669_2 := h669c.2.2.1
                            have p669_3 := h669c.2.2.2
                            linarith only [hlam, p669_0]
                        · linarith only [h499, h502, h668, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h716 | h716
                        · linarith only [h626, h667, h716, hc23, hlam, hphi, u3elo3]
                        · linarith only [h499, h502, h716, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h501, h623, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
            · linarith only [h0, h500, h622, hlam]
          · linarith only [h0, h499, h502, h621, hc01, hlam, hphi, ht12, ht23, u3elo3]
      · linarith only [h499, h501, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h723 | h723
      · rcases m.htr 0 3 4 (by decide) (by decide) with h724 | h724
        · linarith only [h499, h500, h724, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
          · rcases m.htr 1 2 4 (by decide) (by decide) with h727 | h727
            · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
              · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                · linarith only [h724, h729, hc03, hlam, hphi, u3elo1]
                · linarith only [h499, h500, h727, h729, hc23, hlam, hphi, u3elo3]
              · linarith only [h500, h723, h727, h728, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
              · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                · linarith only [h499, h724, h734, hc23, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h736 | h736
                  · linarith only [h499, h734, h736, hc13, hlam, hphi, u3elo0]
                  · linarith only [h499, h500, h736, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h733, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h726, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h499, h723, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h742 | h742
    · rcases m.htr 0 2 5 (by decide) (by decide) with h743 | h743
      · rcases m.htr 0 3 4 (by decide) (by decide) with h744 | h744
        · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
          · rcases m.htr 1 2 4 (by decide) (by decide) with h746 | h746
            · rcases m.htr 1 2 5 (by decide) (by decide) with h747 | h747
              · rcases m.htr 1 3 4 (by decide) (by decide) with h748 | h748
                · rcases m.htr 2 3 4 (by decide) (by decide) with h749 | h749
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h751 | h751
                      · linarith only [h499, h742, h745, h751, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h753 | h753
                        · linarith only [h749, h751, h753, hlam]
                        · rcases h2bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h0, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h499, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h499, h745, h749, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u3elo1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h499, h745, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p755_1, u3elo1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p755_1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h499, h742, h749, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p755_1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            rcases p755_3 (m.d 0 2) (by simp) with h764 | h764
                            · linarith only [h0, h764, hlam]
                            · linarith only [h742, h764, hlam]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            rcases p755_3 (m.d 0 2) (by simp) with h767 | h767
                            · linarith only [h0, h767, hlam]
                            · linarith only [h743, h767, hlam]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h743, h749, h751, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p755_1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h745, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h745, h749, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u3elo1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h745, h749, h751, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p755_1, u3elo1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h742, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h746, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h749, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h751, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h743, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h747, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h750, hlam, p755_0]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [h743, h749, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p755_1]
                          · have p755_0 := h755c.1
                            have p755_1 := h755c.2.1
                            have p755_2 := h755c.2.2.1
                            have p755_3 := h755c.2.2.2
                            linarith only [hlam, p755_0]
                    · linarith only [h499, h750, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h499, h742, h749, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h499, h742, h744, h748, hc13, hlam, hphi, u3elo2]
              · linarith only [h0, h499, h742, h745, h747, hc01, hc24, hlam, hphi, ht12, ht23, ht45, u3elo1, u5elo2]
            · linarith only [h499, h742, h745, h746, hlam]
          · linarith only [h0, h745, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h499, h742, h744, hlam]
      · linarith only [h742, h743, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h793 | h793
      · rcases m.htr 0 3 4 (by decide) (by decide) with h794 | h794
        · rcases m.htr 1 2 3 (by decide) (by decide) with h795 | h795
          · rcases m.htr 1 2 4 (by decide) (by decide) with h796 | h796
            · rcases m.htr 1 2 5 (by decide) (by decide) with h797 | h797
              · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
                · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h802 | h802
                        · rcases h2bigk with h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c | h803c
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h0, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h499, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h742, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h742, h796, h798, h800, h802, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p803_1, u3elo1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h499, h793, h800, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h742, h793, h800, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            rcases p803_3 (m.d 0 2) (by simp) with h813 | h813
                            · linarith only [h0, h813, hlam]
                            · linarith only [h793, h813, hlam]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h793, h800, h802, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h795, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h742, h793, h795, h800, h802, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p803_1, u3elo1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h795, h800, h802, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p803_1, u3elo1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h793, h800, h802, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h796, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h799, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h796, h798, h800, h802, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p803_1, u3elo1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h793, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h797, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h800, hlam, p803_0]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [h801, hlam, p803_1]
                          · have p803_0 := h803c.1
                            have p803_1 := h803c.2.1
                            have p803_2 := h803c.2.2.1
                            have p803_3 := h803c.2.2.2
                            linarith only [hlam, p803_0]
                        · linarith only [h499, h793, h795, h801, h802, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h742, h801, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · linarith only [h499, h793, h800, hc25, hlam, hphi, u5elo3]
                  · linarith only [h499, h793, h794, h799, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h499, h794, h795, h798, hlam]
              · linarith only [h742, h793, h797, hc12, hc24, hlam, hphi]
            · linarith only [h499, h795, h796, hc02, hc24, hlam, hphi]
          · linarith only [h0, h795, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h839 | h839
          · rcases m.htr 1 2 4 (by decide) (by decide) with h840 | h840
            · rcases m.htr 1 2 5 (by decide) (by decide) with h841 | h841
              · rcases m.htr 1 3 4 (by decide) (by decide) with h842 | h842
                · linarith only [h794, h842, hc03, hlam, hphi, u3elo1]
                · linarith only [h499, h793, h839, h842, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h499, h793, h839, h841, hlam]
            · linarith only [h499, h793, h839, h840, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · linarith only [h0, h839, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h848 | h848
        · rcases m.htr 1 2 3 (by decide) (by decide) with h849 | h849
          · rcases m.htr 1 2 4 (by decide) (by decide) with h850 | h850
            · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
              · rcases m.htr 1 3 4 (by decide) (by decide) with h852 | h852
                · rcases m.htr 2 3 4 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h856 | h856
                        · rcases h2bigk with h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h499, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h742, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h793, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h499, hc01, hc12, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h742, hc01, hc12, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h793, hc01, hc12, hlam, hphi, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h849, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h742, h849, hc01, hlam, hphi, ht12, ht23, p857_1, u3elo1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h793, h849, hc01, hlam, hphi, ht12, ht23, p857_1, u3elo1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h850, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h853, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h793, h850, h852, hc01, hlam, hphi, ht12, ht23, p857_1, u3elo1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p857_1, u5elo1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h851, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h854, hlam, p857_0]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [h855, hlam, p857_1]
                          · have p857_0 := h857c.1
                            have p857_1 := h857c.2.1
                            have p857_2 := h857c.2.2.1
                            have p857_3 := h857c.2.2.2
                            linarith only [hlam, p857_0]
                        · rcases h2bigk with h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h499, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h742, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h793, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h499, hc01, hc12, hlam, hphi, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h855, h856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h793, hc01, hc12, hlam, hphi, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h849, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h793, h849, h851, h855, h856, hc01, hc34, hlam, hphi, ht12, ht23, ht45, p883_1, u3elo1, u5elo1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h793, h849, hc01, hlam, hphi, ht12, ht23, p883_1, u3elo1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h850, hc01, hc14, hlam, hphi, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h850, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h853, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h793, h850, h852, hc01, hlam, hphi, ht12, ht23, p883_1, u3elo1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p883_1, u5elo1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h851, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h854, hlam, p883_0]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [h855, hlam, p883_1]
                          · have p883_0 := h883c.1
                            have p883_1 := h883c.2.1
                            have p883_2 := h883c.2.2.1
                            have p883_3 := h883c.2.2.2
                            linarith only [hlam, p883_0]
                      · linarith only [h0, h742, h855, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h0, h499, h854, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h499, h853, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h848, h852, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h499, h849, h850, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h0, h849, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
          · rcases m.htr 1 2 4 (by decide) (by decide) with h917 | h917
            · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
              · rcases m.htr 1 3 4 (by decide) (by decide) with h919 | h919
                · linarith only [h848, h919, hc03, hlam, hphi, u3elo1]
                · linarith only [h0, h499, h916, h919, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h499, h916, h918, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h499, h916, h917, hc01, hc24, hlam, hphi, ht12]
          · linarith only [h0, h916, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_22_13_15_H_I_L_0_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_0_L_0_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_0_L_0_x1 m hb2 hb3 hb5 h0

end R2N4
