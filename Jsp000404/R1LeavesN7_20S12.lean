import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7257 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 5 (by decide) (by decide) with h7619 | h7619
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7620 | h7620
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7621 | h7621
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7622 | h7622
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7623 | h7623
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7624 | h7624
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7625 | h7625
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7626 | h7626
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7627 | h7627
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7628 | h7628
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7629 | h7629
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7630 | h7630
                        · rcases h2bigk with h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c | h7631c
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h0, hlam, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h5034, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7257, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7257, h7622, h7627, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7257, h7619, h7628, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            rcases p7631_3 (m.d 0 2) (by simp) with h7641 | h7641
                            · linarith only [h0, h7641, hlam]
                            · linarith only [h7619, h7641, hlam]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7619, h7622, h7628, h7630, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7622, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7257, h7619, h7622, h7628, h7630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7622, h7628, h7630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7619, h7623, h7628, h7630, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7623, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7627, hlam, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7622, h7627, h7628, h7630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7619, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7624, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7628, hlam, p7631_1]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [h7629, hlam, p7631_0]
                          · have p7631_0 := h7631c.1
                            have p7631_1 := h7631c.2.1
                            have p7631_2 := h7631c.2.2.1
                            have p7631_3 := h7631c.2.2.2
                            linarith only [hlam, p7631_0]
                        · linarith only [h5034, h7619, h7622, h7629, h7630, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h7257, h7619, h7621, h7629, hlam]
                    · linarith only [h7257, h7619, h7627, h7628, hlam]
                  · linarith only [h5034, h7620, h7627, hlam]
                · linarith only [h3667, h7257, h7619, h7621, h7626, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h5034, h7620, h7622, h7625, hlam]
            · linarith only [h5034, h7619, h7622, h7624, hlam]
          · linarith only [h5034, h7622, h7623, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7667 | h7667
          · linarith only [h7257, h7619, h7622, h7667, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7669 | h7669
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7670 | h7670
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7671 | h7671
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7672 | h7672
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7673 | h7673
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7674 | h7674
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7675 | h7675
                        · rcases h2bigk with h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h0, hlam, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h5034, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7257, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h0, h7667, h7672, h7673, h7675, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7667, h7672, hc02, hc23, hlam, hphi, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7622, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7667, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7667, h7672, h7673, h7675, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7619, h7673, h7675, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7257, h7619, h7673, h7675, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            rcases p7676_3 (m.d 0 2) (by simp) with h7691 | h7691
                            · linarith only [h5034, h7691, hlam]
                            · linarith only [h7619, h7691, hlam]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7619, h7673, h7675, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7672, hlam, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            rcases p7676_3 (m.d 0 2) (by simp) with h7698 | h7698
                            · linarith only [h7257, h7698, hlam]
                            · linarith only [h7619, h7698, hlam]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7619, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7669, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7673, hlam, p7676_1]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [h7674, hlam, p7676_0]
                          · have p7676_0 := h7676c.1
                            have p7676_1 := h7676c.2.1
                            have p7676_2 := h7676c.2.2.1
                            have p7676_3 := h7676c.2.2.2
                            linarith only [hlam, p7676_0]
                        · rcases h2bigk with h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c | h7706c
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h0, hlam, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h5034, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7257, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h0, h7667, h7672, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7667, h7672, hc02, hc23, hlam, hphi, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7622, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7667, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7667, h7672, h7674, h7675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7619, h7674, h7675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7257, h7619, h7674, h7675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7674, h7675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7619, h7674, h7675, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h0, h7619, h7674, h7675, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7672, hlam, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7672, h7674, h7675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7619, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7669, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7673, hlam, p7706_1]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [h7674, hlam, p7706_0]
                          · have p7706_0 := h7706c.1
                            have p7706_1 := h7706c.2.1
                            have p7706_2 := h7706c.2.2.1
                            have p7706_3 := h7706c.2.2.2
                            linarith only [hlam, p7706_0]
                      · linarith only [h7257, h7619, h7620, h7621, h7674, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h7667, h7672, h7673, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h7622, h7672, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3667, h7619, h7621, h7622, h7671, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h5034, h7620, h7622, h7670, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h7619, h7669, hlam]
      · linarith only [h7257, h7619, h7621, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7739 | h7739
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7740 | h7740
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7741 | h7741
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7742 | h7742
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7743 | h7743
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7744 | h7744
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7745 | h7745
                  · linarith only [h5034, h7619, h7620, h7740, h7745, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h5034, h7619, h7743, h7745, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h3667, h7739, h7744, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7749 | h7749
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7750 | h7750
                  · linarith only [h5034, h7619, h7620, h7740, h7750, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7752 | h7752
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7753 | h7753
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7754 | h7754
                        · rcases h2bigk with h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c | h7755c
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h0, hlam, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h5034, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7257, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h5034, h7752, h7754, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h5034, h7619, h7752, h7754, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7257, h7619, h7752, h7754, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            rcases p7755_3 (m.d 0 2) (by simp) with h7765 | h7765
                            · linarith only [h0, h7765, hlam]
                            · linarith only [h7619, h7765, hlam]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7619, h7752, h7754, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7740, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7750, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7740, h7743, h7752, h7754, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7619, h7741, h7752, h7754, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7741, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7741, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7741, h7752, h7754, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7619, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7742, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7752, hlam, p7755_1]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [h7753, hlam, p7755_0]
                          · have p7755_0 := h7755c.1
                            have p7755_1 := h7755c.2.1
                            have p7755_2 := h7755c.2.2.1
                            have p7755_3 := h7755c.2.2.2
                            linarith only [hlam, p7755_0]
                        · linarith only [h5034, h7619, h7740, h7743, h7752, h7754, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h3667, h5034, h7257, h7619, h7739, h7740, h7743, h7753, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h5034, h7619, h7752, hlam]
                · linarith only [h3667, h7739, h7749, hlam]
            · linarith only [h5034, h7257, h7619, h7740, h7741, h7742, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h5034, h7740, h7741, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7789 | h7789
          · linarith only [h7257, h7619, h7740, h7789, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7791 | h7791
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7792 | h7792
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7793 | h7793
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7794 | h7794
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7795 | h7795
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7796 | h7796
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7797 | h7797
                        · rcases h2bigk with h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c | h7798c
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h0, hlam, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h5034, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7257, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h5034, h7620, h7792, h7795, h7797, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7789, h7794, hc02, hc23, hlam, hphi, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7740, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7789, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7789, h7794, h7795, h7797, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7619, h7795, h7797, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7257, h7619, h7795, h7797, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            rcases p7798_3 (m.d 0 2) (by simp) with h7813 | h7813
                            · linarith only [h5034, h7813, hlam]
                            · linarith only [h7619, h7813, hlam]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7619, h7795, h7797, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7794, hlam, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            rcases p7798_3 (m.d 0 2) (by simp) with h7820 | h7820
                            · linarith only [h7257, h7820, hlam]
                            · linarith only [h7619, h7820, hlam]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7619, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7791, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7795, hlam, p7798_1]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [h7796, hlam, p7798_0]
                          · have p7798_0 := h7798c.1
                            have p7798_1 := h7798c.2.1
                            have p7798_2 := h7798c.2.2.1
                            have p7798_3 := h7798c.2.2.2
                            linarith only [hlam, p7798_0]
                        · linarith only [h5034, h7619, h7620, h7739, h7797, hc04, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h7789, h7796, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h5034, h7620, h7740, h7792, h7795, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h7740, h7792, h7794, hlam]
                · linarith only [h3667, h5034, h7619, h7620, h7739, h7792, h7793, hc01, hc13, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7833 | h7833
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7834 | h7834
                  · linarith only [h0, h7740, h7792, h7834, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h7740, h7834, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3667, h7619, h7739, h7740, h7833, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h7619, h7791, hlam]
      · linarith only [h5034, h7619, h7620, h7739, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7840 | h7840
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7841 | h7841
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7842 | h7842
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7843 | h7843
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7844 | h7844
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7845 | h7845
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7846 | h7846
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7847 | h7847
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7848 | h7848
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7849 | h7849
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7850 | h7850
                        · rcases h2bigk with h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c | h7851c
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, hlam, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h5034, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7257, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7619, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7257, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7619, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7842, hc01, hc13, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7842, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7619, h7842, h7849, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7619, h7842, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7843, hc01, hc14, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7843, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7847, hlam, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7619, h7842, h7847, hc01, hc12, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h0, h7844, hc01, hc15, hlam, hphi, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7844, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7848, hlam, p7851_1]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [h7849, hlam, p7851_0]
                          · have p7851_0 := h7851c.1
                            have p7851_1 := h7851c.2.1
                            have p7851_2 := h7851c.2.2.1
                            have p7851_3 := h7851c.2.2.2
                            linarith only [hlam, p7851_0]
                        · rcases h2bigk with h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c | h7877c
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, hlam, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h5034, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7257, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7619, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7257, h7841, h7847, h7850, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7257, h7841, h7850, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, h7619, hc01, hc12, hlam, hphi, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7842, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7257, h7841, h7842, h7850, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, h7619, h7842, hc01, hc12, hlam, hphi, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7843, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7847, hlam, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, h7619, h7842, h7847, hc01, hc12, hlam, hphi, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7844, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7848, hlam, p7877_1]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [h7849, hlam, p7877_0]
                          · have p7877_0 := h7877c.1
                            have p7877_1 := h7877c.2.1
                            have p7877_2 := h7877c.2.2.1
                            have p7877_3 := h7877c.2.2.2
                            linarith only [hlam, p7877_0]
                      · linarith only [h0, h3667, h7257, h7841, h7842, h7845, h7849, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7904 | h7904
                      · linarith only [h7847, h7848, h7904, hlam]
                      · linarith only [h0, h3667, h7257, h7841, h7842, h7845, h7904, hc01, hc12, hlam, hphi]
                  · linarith only [h5034, h7840, h7847, hlam]
                · linarith only [h3667, h5034, h7840, h7841, h7846, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h5034, h7840, h7842, h7845, hlam]
            · linarith only [h0, h5034, h7842, h7844, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h5034, h7842, h7843, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7912 | h7912
          · linarith only [h0, h7257, h7842, h7912, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7914 | h7914
            · linarith only [h0, h7619, h7842, h7914, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7916 | h7916
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7917 | h7917
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7918 | h7918
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7919 | h7919
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7920 | h7920
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7921 | h7921
                        · rcases h2bigk with h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c | h7922c
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hlam, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h5034, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7257, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7619, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, h7914, h7918, h7920, hc01, hc23, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7842, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7912, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7914, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, h7257, hc01, hc23, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, h7914, hc01, hc23, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7918, hlam, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, h7914, h7918, hc01, hc23, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7919, hlam, p7922_1]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [h7920, hlam, p7922_0]
                          · have p7922_0 := h7922c.1
                            have p7922_1 := h7922c.2.1
                            have p7922_2 := h7922c.2.2.1
                            have p7922_3 := h7922c.2.2.2
                            linarith only [hlam, p7922_0]
                        · rcases h2bigk with h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c | h7948c
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hlam, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h5034, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7257, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7619, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7842, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7912, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7914, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, h7257, hc01, hc23, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, h7914, hc01, hc23, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7918, hlam, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, h7914, h7918, hc01, hc23, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7919, hlam, p7948_1]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [h7920, hlam, p7948_0]
                          · have p7948_0 := h7948c.1
                            have p7948_1 := h7948c.2.1
                            have p7948_2 := h7948c.2.2.1
                            have p7948_3 := h7948c.2.2.2
                            linarith only [hlam, p7948_0]
                      · linarith only [h0, h3667, h7257, h7841, h7842, h7916, h7920, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h7842, h7919, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h5034, h7840, h7918, hlam]
                · linarith only [h3667, h7841, h7917, hlam]
              · linarith only [h0, h5034, h7840, h7842, h7916, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h7979 | h7979
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7980 | h7980
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7981 | h7981
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7982 | h7982
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7983 | h7983
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7984 | h7984
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7985 | h7985
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7986 | h7986
                      · linarith only [h3667, h7841, h7980, h7986, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h7257, h7979, h7982, h7983, h7986, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7989 | h7989
                      · linarith only [h0, h7257, h7841, h7980, h7989, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h7257, h7979, h7982, h7983, h7989, hc01, hc12, hlam, hphi]
                  · linarith only [h5034, h7840, h7984, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h7993 | h7993
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h7994 | h7994
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7995 | h7995
                      · linarith only [h7980, h7983, h7995, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7997 | h7997
                        · linarith only [h3667, h7840, h7983, h7997, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c | h7999c
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, hlam, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h5034, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7257, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7619, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, h7257, hc01, hc12, hlam, hphi, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, h7257, h7995, hc01, hc12, hlam, hphi, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7979, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7257, h7979, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, h7257, h7979, h7995, hc01, hc12, hlam, hphi, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7980, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7993, hlam, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7995, hlam, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7981, hlam, p7999_0]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h7994, hlam, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [h0, h7257, hc01, hc25, hlam, hphi, ht12, p7999_1]
                          · have p7999_0 := h7999c.1
                            have p7999_1 := h7999c.2.1
                            have p7999_2 := h7999c.2.2.1
                            have p7999_3 := h7999c.2.2.2
                            linarith only [hlam, p7999_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8025 | h8025
                      · linarith only [h3667, h7983, h8025, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8027 | h8027
                        · linarith only [h0, h5034, h7257, h7840, h7980, h7983, h7994, h8027, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases h2bigk with h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c | h8029c
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, hlam, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h5034, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7257, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7619, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h5034, h7840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7257, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7619, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7979, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7257, h7979, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7994, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7980, hc01, hc14, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7980, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7993, hlam, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h8025, hlam, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h7981, hlam, p8029_0]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7257, h7981, h7993, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [h0, h7257, h7981, hc01, hc12, hlam, hphi, p8029_1]
                          · have p8029_0 := h8029c.1
                            have p8029_1 := h8029c.2.1
                            have p8029_2 := h8029c.2.2.1
                            have p8029_3 := h8029c.2.2.2
                            linarith only [hlam, p8029_0]
                  · linarith only [h5034, h7840, h7993, hlam]
              · linarith only [h0, h5034, h7619, h7840, h7841, h7979, h7981, h7982, hc01, hc12, hlam, hphi]
            · linarith only [h0, h5034, h7979, h7981, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h5034, h7979, h7980, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8059 | h8059
          · linarith only [h0, h7257, h7979, h8059, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8061 | h8061
            · linarith only [h0, h7619, h7979, h8061, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8063 | h8063
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8064 | h8064
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8065 | h8065
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8066 | h8066
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8067 | h8067
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8068 | h8068
                        · linarith only [h0, h5034, h7257, h7840, h7841, h8068, hc01, hc23, hlam, hphi, ht12]
                        · rcases h2bigk with h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hlam, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h5034, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h7257, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h7619, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, h8061, h8065, h8067, hc01, hc23, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h7979, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h8059, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h8061, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, h7257, hc01, hc23, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, h8061, hc01, hc23, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h8065, hlam, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, h8061, h8065, hc01, hc23, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h8066, hlam, p8070_1]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [h8067, hlam, p8070_0]
                          · have p8070_0 := h8070c.1
                            have p8070_1 := h8070c.2.1
                            have p8070_2 := h8070c.2.2.1
                            have p8070_3 := h8070c.2.2.2
                            linarith only [hlam, p8070_0]
                      · linarith only [h0, h7257, h8063, h8064, h8067, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h7257, h7841, h7979, h8063, h8064, h8066, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h7840, h7841, h7979, h8063, h8064, h8065, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8099 | h8099
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8100 | h8100
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8101 | h8101
                      · linarith only [h3667, h8064, h8101, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h8059, h8101, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h7979, h8100, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h7979, h8099, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h5034, h7840, h7979, h8063, hc01, hc23, hlam, hphi, ht12]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h8107 | h8107
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8108 | h8108
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8109 | h8109
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8110 | h8110
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8111 | h8111
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8112 | h8112
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8113 | h8113
                  · linarith only [h0, h5034, h7840, h8108, h8113, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h5034, h8111, h8113, hc01, hc13, hlam, hphi]
                · linarith only [h7257, h8107, h8109, h8112, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8117 | h8117
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8118 | h8118
                  · linarith only [h8108, h8111, h8118, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8120 | h8120
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8121 | h8121
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8122 | h8122
                        · rcases h2bigk with h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c | h8123c
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, hlam, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h5034, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h7257, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h7619, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h7619, h8120, hc01, hc12, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h3667, h7257, hc01, hc12, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h7619, hc01, hc12, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h8108, hc01, hc13, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8108, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8118, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h7619, h8108, h8111, hc01, hc34, hlam, hphi, ht12, ht23, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8109, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8109, h8120, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h7619, h8109, hc01, hc12, hlam, hphi, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h0, h8120, hc01, hc23, hlam, hphi, ht12, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8110, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8120, hlam, p8123_1]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [h8121, hlam, p8123_0]
                          · have p8123_0 := h8123c.1
                            have p8123_1 := h8123c.2.1
                            have p8123_2 := h8123c.2.2.1
                            have p8123_3 := h8123c.2.2.2
                            linarith only [hlam, p8123_0]
                        · linarith only [h3667, h8107, h8111, h8122, hlam]
                      · linarith only [h7257, h8107, h8121, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8151 | h8151
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8152 | h8152
                        · rcases h2bigk with h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c | h8153c
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, hlam, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h5034, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h7257, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h7619, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, h5034, hc01, hc12, hlam, hphi, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h7257, h8107, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, h5034, h8120, hc01, hc12, hlam, hphi, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, h8108, hc01, hc13, hlam, hphi, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8108, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8118, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8120, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8109, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8109, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8110, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h0, h5034, h8110, hc01, hc12, hlam, hphi, p8153_1]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [h8151, hlam, p8153_0]
                          · have p8153_0 := h8153c.1
                            have p8153_1 := h8153c.2.1
                            have p8153_2 := h8153c.2.2.1
                            have p8153_3 := h8153c.2.2.2
                            linarith only [hlam, p8153_0]
                        · linarith only [h3667, h8107, h8111, h8152, hlam]
                      · linarith only [h7257, h8107, h8151, hlam]
                · linarith only [h3667, h7257, h8107, h8109, h8117, hc01, hc12, hlam, hphi]
            · linarith only [h0, h7257, h8109, h8110, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h5034, h8108, h8109, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8184 | h8184
          · linarith only [h0, h7257, h8108, h8184, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8186 | h8186
            · linarith only [h0, h7619, h8108, h8186, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8188 | h8188
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8189 | h8189
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8190 | h8190
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8191 | h8191
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8192 | h8192
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8193 | h8193
                        · rcases h2bigk with h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c | h8194c
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hlam, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h5034, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h7257, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h7619, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, h8186, h8190, h8192, hc01, hc23, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8108, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8184, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8186, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hc12, hc23, hlam, hphi, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, h7257, hc01, hc23, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, h8186, hc01, hc23, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8190, hlam, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, h8186, h8190, hc01, hc23, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8191, hlam, p8194_1]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [h8192, hlam, p8194_0]
                          · have p8194_0 := h8194c.1
                            have p8194_1 := h8194c.2.1
                            have p8194_2 := h8194c.2.2.1
                            have p8194_3 := h8194c.2.2.2
                            linarith only [hlam, p8194_0]
                        · linarith only [h0, h3667, h5034, h7840, h8107, h8193, hc01, hc14, hlam, hphi]
                      · linarith only [h3667, h7840, h8107, h8108, h8184, h8188, h8192, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5034, h7840, h8108, h8188, h8191, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h8108, h8188, h8190, hlam]
                · linarith only [h7840, h8107, h8188, h8189, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8225 | h8225
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8226 | h8226
                  · linarith only [h0, h8108, h8188, h8226, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h8108, h8226, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3667, h8107, h8225, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8230 | h8230
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8231 | h8231
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8232 | h8232
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8233 | h8233
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8234 | h8234
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8235 | h8235
                  · linarith only [h0, h5034, h7840, h8230, h8235, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h5034, h8233, h8235, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8238 | h8238
                  · linarith only [h0, h5034, h7840, h8230, h8238, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h5034, h8233, h8234, h8238, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8241 | h8241
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8242 | h8242
                  · linarith only [h0, h5034, h7840, h8107, h8230, h8233, h8241, h8242, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8244 | h8244
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8245 | h8245
                      · linarith only [h0, h5034, h7840, h8107, h8231, h8245, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h7257, h8241, h8245, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8248 | h8248
                      · linarith only [h0, h5034, h7840, h8107, h8231, h8248, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h7257, h8233, h8241, h8248, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8251 | h8251
                  · linarith only [h0, h5034, h7840, h8230, h8251, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8253 | h8253
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8254 | h8254
                      · linarith only [h3667, h8241, h8254, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h8251, h8253, h8254, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8257 | h8257
                      · linarith only [h3667, h8241, h8257, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8259 | h8259
                        · linarith only [h0, h5034, h8230, h8233, h8241, h8259, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h5034, h8230, h8233, h8259, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h5034, h8230, h8232, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h5034, h8230, h8231, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h8264 | h8264
          · linarith only [h0, h7257, h8230, h8264, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8266 | h8266
            · linarith only [h0, h7619, h8230, h8266, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h8268 | h8268
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8269 | h8269
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8270 | h8270
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8271 | h8271
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8272 | h8272
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8273 | h8273
                        · linarith only [h0, h5034, h7840, h8107, h8230, h8268, h8273, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h5034, h7840, h8230, h8268, h8269, h8273, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h7257, h8230, h8268, h8269, h8272, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5034, h7840, h8107, h8230, h8268, h8269, h8271, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h5034, h7840, h8107, h8230, h8268, h8269, h8270, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8279 | h8279
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8280 | h8280
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8281 | h8281
                      · linarith only [h3667, h8269, h8281, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h8264, h8281, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h5034, h7840, h8230, h8268, h8280, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h8230, h8268, h8279, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8286 | h8286
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8287 | h8287
                  · linarith only [h0, h8230, h8268, h8287, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h8230, h8287, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8290 | h8290
                  · linarith only [h0, h8230, h8268, h8290, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h8230, h8290, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 4 (by decide) (by decide) with h7257 | h7257
  · exact r1l7_22_14_H_I_L_I_s3_x1_x0 m hb2 hb4 hg0 hg3667 h5034 h7257
  · exact r1l7_22_14_H_I_L_I_s3_x1_x1 m hb2 hb4 hg0 hg3667 h5034 h7257

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 3 (by decide) (by decide) with h5034 | h5034
  · exact r1l7_22_14_H_I_L_I_s3_x0 m hb2 hb4 hg0 hg3667 h5034
  · exact r1l7_22_14_H_I_L_I_s3_x1 m hb2 hb4 hg0 hg3667 h5034

end R2N4
