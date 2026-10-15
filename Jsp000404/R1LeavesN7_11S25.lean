import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S14
import Jsp000404.R1LeavesN7_11S23
import Jsp000404.R1LeavesN7_11S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h9574 | h9574
  · rcases m.htr 0 2 4 (by decide) (by decide) with h9575 | h9575
    · rcases m.htr 0 2 5 (by decide) (by decide) with h9576 | h9576
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9577 | h9577
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9578 | h9578
          · linarith only [h8410, h8411, h9578, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9580 | h9580
            · linarith only [h8410, h8411, h9577, h9580, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9582 | h9582
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9583 | h9583
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9584 | h9584
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9585 | h9585
                    · linarith only [h8410, h8411, h9578, h9583, h9585, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9587 | h9587
                      · linarith only [h9580, h9587, hc14, hlam, hphi, ht01, u0ehi3]
                      · linarith only [h8410, h8411, h9584, h9587, hc34, hc45, hlam, hphi]
                  · linarith only [h9577, h9578, h9582, h9584, hc23, hc35, hlam, hphi]
                · linarith only [h0, h8410, h9576, h9577, h9583, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h8410, h9577, h9582, hc23, hlam, hphi, ht01, ht12, u0ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9593 | h9593
          · linarith only [h8410, h8411, h9593, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9595 | h9595
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9596 | h9596
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9597 | h9597
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9598 | h9598
                  · linarith only [h8410, h8411, h9577, h9597, h9598, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9600 | h9600
                    · linarith only [h8410, h8411, h9593, h9597, h9600, hc12, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9602 | h9602
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9603 | h9603
                        · linarith only [h8410, h8411, h9596, h9598, h9602, h9603, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9605 | h9605
                          · linarith only [h8410, h8411, h9593, h9596, h9598, h9602, h9605, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h9607 | h9607
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9608 | h9608
                              · rcases h2bigk with h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c | h9609c
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h0, hlam, p9609_1]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9612 | h9612
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9613 | h9613
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9614 | h9614
                                      · linarith only [h9614, hlam, p9609_0]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9616 | h9616
                                        · linarith only [h9575, h9616, hlam]
                                        · linarith only [h9603, h9616, hlam]
                                    · linarith only [h9596, h9613, hlam]
                                  · linarith only [h9612, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9621 | h9621
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9622 | h9622
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9623 | h9623
                                      · linarith only [h9574, h9623, hlam]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9625 | h9625
                                        · linarith only [h9625, hlam, p9609_0]
                                        · rcases p9609_3 (m.d 2 5) (by simp) with h9627 | h9627
                                          · linarith only [h9576, h9627, hlam]
                                          · rcases h3bigk with h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c | h9629c
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h8410, h8411, h9598, h9602, hc13, hc34, hlam, hphi, p9629_1]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h8410, h8411, h9598, h9602, hc23, hc34, hlam, hphi, p9629_1]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9577, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9593, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h8410, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h8410, h8411, h9598, h9602, hc23, hc34, hlam, hphi, p9629_1]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9598, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9600, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9574, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9596, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9603, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9605, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9629_1, u0ehi2]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              rcases p9629_3 (m.d 0 3) (by simp) with h9646 | h9646
                                              · linarith only [h9577, h9646, hlam]
                                              · linarith only [h8410, h9646, hlam]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              rcases p9629_3 (m.d 0 3) (by simp) with h9649 | h9649
                                              · linarith only [h9577, h9649, hlam]
                                              · linarith only [h9574, h9649, hlam]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h8411, h9600, hc01, hc34, hlam, hphi, ht12, ht23, p9629_1]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p9629_1, u0ehi2]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              rcases p9629_3 (m.d 0 3) (by simp) with h9655 | h9655
                                              · linarith only [h9593, h9655, hlam]
                                              · linarith only [h8410, h9655, hlam]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              rcases p9629_3 (m.d 0 3) (by simp) with h9658 | h9658
                                              · linarith only [h9593, h9658, hlam]
                                              · linarith only [h9574, h9658, hlam]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [h9608, hlam, p9629_0]
                                            · have p9629_0 := h9629c.1
                                              have p9629_1 := h9629c.2.1
                                              have p9629_2 := h9629c.2.2.1
                                              have p9629_3 := h9629c.2.2.2
                                              linarith only [hlam, p9629_0]
                                    · linarith only [h0, h9622, hlam, p9609_1]
                                  · linarith only [h9621, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9665 | h9665
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9666 | h9666
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9667 | h9667
                                      · linarith only [h9574, h9667, hlam]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9669 | h9669
                                        · linarith only [h9575, h9669, hlam]
                                        · linarith only [h9607, h9669, hlam]
                                    · linarith only [h9597, h9666, hlam]
                                  · linarith only [h9665, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, p9609_1, u0ehi1]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9676 | h9676
                                  · linarith only [h0, h9676, hlam]
                                  · linarith only [h9574, h9676, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9679 | h9679
                                  · linarith only [h0, h9679, hlam]
                                  · linarith only [h9575, h9679, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9682 | h9682
                                  · linarith only [h0, h9682, hlam]
                                  · linarith only [h9576, h9682, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9574, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9596, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9603, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9605, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9575, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h0, h8410, hc24, hlam, hphi, ht01, ht12, p9609_1, u0ehi2]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9692 | h9692
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9693 | h9693
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9694 | h9694
                                      · linarith only [h9603, h9694, hlam]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9696 | h9696
                                        · rcases p9609_3 (m.d 2 5) (by simp) with h9697 | h9697
                                          · linarith only [h9607, h9697, hlam]
                                          · linarith only [h9605, h9697, hlam]
                                        · linarith only [h9603, h9696, hlam]
                                    · linarith only [h9596, h9693, hlam]
                                  · linarith only [h9574, h9692, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9704 | h9704
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9705 | h9705
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9706 | h9706
                                      · linarith only [h9603, h9706, hlam]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9708 | h9708
                                        · rcases p9609_3 (m.d 2 5) (by simp) with h9709 | h9709
                                          · linarith only [h9607, h9709, hlam]
                                          · rcases h3bigk with h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c | h9711c
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9577, h9596, hc23, hc34, hlam, hphi, p9711_1]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9577, hc23, hc34, hlam, hphi, p9711_1]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9577, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9593, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h8410, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h8410, h8411, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9711_1]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9598, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9600, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9574, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9596, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9603, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9605, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9711_1, u0ehi2]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              rcases p9711_3 (m.d 0 3) (by simp) with h9728 | h9728
                                              · linarith only [h9577, h9728, hlam]
                                              · linarith only [h8410, h9728, hlam]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              rcases p9711_3 (m.d 0 3) (by simp) with h9731 | h9731
                                              · linarith only [h9577, h9731, hlam]
                                              · linarith only [h9574, h9731, hlam]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h0, h8411, h9575, h9600, h9605, hc01, hc12, hc23, hc34, hlam, hphi, p9609_1, p9711_1]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p9711_1, u0ehi2]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              rcases p9711_3 (m.d 0 3) (by simp) with h9737 | h9737
                                              · linarith only [h9593, h9737, hlam]
                                              · linarith only [h8410, h9737, hlam]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              rcases p9711_3 (m.d 0 3) (by simp) with h9740 | h9740
                                              · linarith only [h9593, h9740, hlam]
                                              · linarith only [h9574, h9740, hlam]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [h9608, hlam, p9711_0]
                                            · have p9711_0 := h9711c.1
                                              have p9711_1 := h9711c.2.1
                                              have p9711_2 := h9711c.2.2.1
                                              have p9711_3 := h9711c.2.2.2
                                              linarith only [hlam, p9711_0]
                                        · linarith only [h9607, h9708, hlam]
                                    · linarith only [h9597, h9705, hlam]
                                  · linarith only [h9576, h9704, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9576, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9597, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  rcases p9609_3 (m.d 0 2) (by simp) with h9750 | h9750
                                  · rcases p9609_3 (m.d 1 2) (by simp) with h9751 | h9751
                                    · rcases p9609_3 (m.d 2 3) (by simp) with h9752 | h9752
                                      · linarith only [h9605, h9752, hlam]
                                      · rcases p9609_3 (m.d 2 4) (by simp) with h9754 | h9754
                                        · rcases p9609_3 (m.d 2 5) (by simp) with h9755 | h9755
                                          · rcases h3bigk with h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c | h9756c
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h8410, h8411, h9596, h9600, h9608, hc23, hc34, hlam, hphi, p9756_1]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h8410, h8411, h9600, h9608, hc23, hc34, hlam, hphi, p9756_1]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9577, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9593, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h8410, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h8410, h8411, h9600, h9608, hc23, hc34, hlam, hphi, p9756_1]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9598, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9600, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9574, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9596, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9603, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9605, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9756_1, u0ehi2]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              rcases p9756_3 (m.d 0 3) (by simp) with h9773 | h9773
                                              · linarith only [h9577, h9773, hlam]
                                              · linarith only [h8410, h9773, hlam]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              rcases p9756_3 (m.d 0 3) (by simp) with h9776 | h9776
                                              · linarith only [h9577, h9776, hlam]
                                              · linarith only [h9574, h9776, hlam]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h0, h8410, h8411, h9575, h9600, h9607, hc12, hc23, hc34, hlam, hphi, ht01, p9609_1, p9756_1, u0ehi2]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h0, h9575, h9607, hc12, hc23, hc35, hlam, hphi, ht01, p9609_1, p9756_1, u0ehi2]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              rcases p9756_3 (m.d 0 3) (by simp) with h9782 | h9782
                                              · linarith only [h9593, h9782, hlam]
                                              · linarith only [h8410, h9782, hlam]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              rcases p9756_3 (m.d 0 3) (by simp) with h9785 | h9785
                                              · linarith only [h9593, h9785, hlam]
                                              · linarith only [h9574, h9785, hlam]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [h9608, hlam, p9756_0]
                                            · have p9756_0 := h9756c.1
                                              have p9756_1 := h9756c.2.1
                                              have p9756_2 := h9756c.2.2.1
                                              have p9756_3 := h9756c.2.2.2
                                              linarith only [hlam, p9756_0]
                                          · linarith only [h9605, h9755, hlam]
                                        · linarith only [h9603, h9754, hlam]
                                    · linarith only [h9596, h9751, hlam]
                                  · linarith only [h9574, h9750, hlam]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [h9607, hlam, p9609_0]
                                · have p9609_0 := h9609c.1
                                  have p9609_1 := h9609c.2.1
                                  have p9609_2 := h9609c.2.2.1
                                  have p9609_3 := h9609c.2.2.2
                                  linarith only [hlam, p9609_0]
                              · linarith only [h9577, h9608, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9797 | h9797
                              · rcases h2bigk with h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c | h9798c
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h0, hlam, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9801 | h9801
                                  · rcases p9798_3 (m.d 1 2) (by simp) with h9802 | h9802
                                    · rcases p9798_3 (m.d 2 3) (by simp) with h9803 | h9803
                                      · linarith only [h9803, hlam, p9798_0]
                                      · rcases p9798_3 (m.d 2 4) (by simp) with h9805 | h9805
                                        · linarith only [h9575, h9805, hlam]
                                        · linarith only [h9603, h9805, hlam]
                                    · linarith only [h9596, h9802, hlam]
                                  · linarith only [h9801, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9810 | h9810
                                  · rcases p9798_3 (m.d 1 2) (by simp) with h9811 | h9811
                                    · rcases p9798_3 (m.d 2 3) (by simp) with h9812 | h9812
                                      · linarith only [h9574, h9812, hlam]
                                      · rcases p9798_3 (m.d 2 4) (by simp) with h9814 | h9814
                                        · linarith only [h9814, hlam, p9798_0]
                                        · rcases p9798_3 (m.d 2 5) (by simp) with h9816 | h9816
                                          · linarith only [h9576, h9816, hlam]
                                          · linarith only [h9607, h9816, hlam]
                                    · linarith only [h0, h9577, h9595, h9607, h9811, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                  · linarith only [h9810, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9821 | h9821
                                  · rcases p9798_3 (m.d 1 2) (by simp) with h9822 | h9822
                                    · rcases p9798_3 (m.d 2 3) (by simp) with h9823 | h9823
                                      · linarith only [h9574, h9823, hlam]
                                      · rcases p9798_3 (m.d 2 4) (by simp) with h9825 | h9825
                                        · linarith only [h9575, h9825, hlam]
                                        · rcases p9798_3 (m.d 2 5) (by simp) with h9827 | h9827
                                          · linarith only [h9827, hlam, p9798_0]
                                          · rcases h3bigk with h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c | h9829c
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h8410, h8411, h9600, hc13, hc35, hlam, hphi, p9829_1]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h8410, h8411, h9600, hc23, hc35, hlam, hphi, p9829_1]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9577, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9593, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h8410, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h8410, h8411, h9600, hc23, hc35, hlam, hphi, p9829_1]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9598, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9600, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9574, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9596, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9603, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9605, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p9829_1, u0ehi2]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              rcases p9829_3 (m.d 0 3) (by simp) with h9846 | h9846
                                              · linarith only [h9577, h9846, hlam]
                                              · linarith only [h8410, h9846, hlam]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              rcases p9829_3 (m.d 0 3) (by simp) with h9849 | h9849
                                              · linarith only [h9577, h9849, hlam]
                                              · linarith only [h9574, h9849, hlam]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9593, hc34, hlam, hphi, ht01, ht12, ht23, p9829_1, u0ehi2]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p9829_1, u0ehi2]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              rcases p9829_3 (m.d 0 3) (by simp) with h9855 | h9855
                                              · linarith only [h9593, h9855, hlam]
                                              · linarith only [h8410, h9855, hlam]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              rcases p9829_3 (m.d 0 3) (by simp) with h9858 | h9858
                                              · linarith only [h9593, h9858, hlam]
                                              · linarith only [h9574, h9858, hlam]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [h9797, hlam, p9829_0]
                                            · have p9829_0 := h9829c.1
                                              have p9829_1 := h9829c.2.1
                                              have p9829_2 := h9829c.2.2.1
                                              have p9829_3 := h9829c.2.2.2
                                              linarith only [hlam, p9829_0]
                                    · linarith only [h9597, h9822, hlam]
                                  · linarith only [h9821, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9575, h9595, h9607, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9867 | h9867
                                  · linarith only [h0, h9867, hlam]
                                  · linarith only [h9574, h9867, hlam]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9870 | h9870
                                  · linarith only [h0, h9870, hlam]
                                  · linarith only [h9575, h9870, hlam]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  rcases p9798_3 (m.d 0 2) (by simp) with h9873 | h9873
                                  · linarith only [h0, h9873, hlam]
                                  · linarith only [h9576, h9873, hlam]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9574, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9596, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9603, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9605, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9575, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9575, h9595, h9607, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9577, h9595, h9607, hc23, hc34, hlam, hphi, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9607, hlam, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9576, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9597, hlam, p9798_0]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9577, h9595, h9607, hc23, hc34, hlam, hphi, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [h9577, h9595, h9603, h9607, hc23, hc34, hlam, hphi, p9798_1]
                                · have p9798_0 := h9798c.1
                                  have p9798_1 := h9798c.2.1
                                  have p9798_2 := h9798c.2.2.1
                                  have p9798_3 := h9798c.2.2.2
                                  linarith only [hlam, p9798_0]
                              · linarith only [h9577, h9595, h9797, hlam]
                      · linarith only [h8410, h8411, h9577, h9595, h9602, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                · linarith only [h0, h8410, h9597, hc25, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h8410, h9596, hc23, hlam, hphi, ht01, ht12, u0ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9895 | h9895
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9896 | h9896
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9897 | h9897
                  · linarith only [h8410, h8411, h9577, h9896, h9897, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9899 | h9899
                    · linarith only [h8410, h8411, h9593, h9896, h9899, hc12, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9901 | h9901
                      · linarith only [h9595, h9901, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9903 | h9903
                        · linarith only [h8410, h8411, h9577, h9895, h9901, h9903, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9905 | h9905
                          · linarith only [h8410, h8411, h9593, h9895, h9901, h9905, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h9907 | h9907
                            · linarith only [h8411, h9901, h9907, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9909 | h9909
                              · linarith only [h8410, h8411, h9901, h9909, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                              · linarith only [h9577, h9909, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                · linarith only [h0, h8410, h9896, hc25, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h8410, h9895, hc23, hlam, hphi, ht01, ht12, u0ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9914 | h9914
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9915 | h9915
          · linarith only [h8410, h8411, h9915, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9917 | h9917
            · linarith only [h0, h8410, h9576, h9914, h9917, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9919 | h9919
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9920 | h9920
                · linarith only [h0, h9576, h9920, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h8410, h9914, h9920, hc25, hlam, hphi, ht01, ht12, u0ehi3]
              · linarith only [h0, h8410, h9914, h9919, hc23, hlam, hphi, ht01, ht12, u0ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9924 | h9924
          · linarith only [h0, h8410, h9576, h9924, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9926 | h9926
            · linarith only [h9575, h9576, h9926, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9928 | h9928
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9929 | h9929
                · linarith only [h0, h9576, h9929, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h8410, h9929, hc25, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h8410, h9928, hc23, hlam, hphi, ht01, ht12, u0ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h9933 | h9933
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9934 | h9934
        · linarith only [h8410, h8411, h9575, h9933, h9934, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9936 | h9936
          · linarith only [h8410, h8411, h9936, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9938 | h9938
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9939 | h9939
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9940 | h9940
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9941 | h9941
                  · linarith only [h8410, h9934, h9941, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9943 | h9943
                    · linarith only [h8410, h8411, h9575, h9933, h9936, h9943, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h9945 | h9945
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h9946 | h9946
                        · linarith only [h8410, h8411, h9939, h9941, h9945, h9946, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h9948 | h9948
                          · linarith only [h8410, h8411, h9575, h9933, h9936, h9939, h9946, h9948, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h9950 | h9950
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h9951 | h9951
                              · rcases h2bigk with h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c | h9952c
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h0, hlam, p9952_1]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9575, h9946, hc23, hc34, hlam, hphi, p9952_1]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9575, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9575, h9946, h9948, hc23, hc34, hlam, hphi, p9952_1]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h8411, h9933, hc12, hlam, hphi, ht01, p9952_1, u0ehi0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  rcases p9952_3 (m.d 0 2) (by simp) with h9960 | h9960
                                  · linarith only [h0, h9960, hlam]
                                  · linarith only [h9574, h9960, hlam]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h8410, h8411, h9575, h9933, hc12, hlam, hphi, ht01, p9952_1, u0ehi2]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  rcases p9952_3 (m.d 0 2) (by simp) with h9964 | h9964
                                  · linarith only [h0, h9964, hlam]
                                  · linarith only [h9933, h9964, hlam]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9574, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9939, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9946, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9948, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h8410, h8411, h9933, h9946, hc34, hlam, hphi, ht01, ht12, ht23, p9952_1, u0ehi2]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h0, h8410, h9946, hc34, hlam, hphi, ht01, ht12, ht23, p9952_1, u0ehi2]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  rcases p9952_3 (m.d 0 2) (by simp) with h9974 | h9974
                                  · linarith only [h9575, h9974, hlam]
                                  · linarith only [h9574, h9974, hlam]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  rcases p9952_3 (m.d 0 2) (by simp) with h9978 | h9978
                                  · linarith only [h9575, h9978, hlam]
                                  · linarith only [h9933, h9978, hlam]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9933, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9940, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9575, h9933, h9946, hc23, hc34, hlam, hphi, p9952_1]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [h9950, hlam, p9952_0]
                                · have p9952_0 := h9952c.1
                                  have p9952_1 := h9952c.2.1
                                  have p9952_2 := h9952c.2.2.1
                                  have p9952_3 := h9952c.2.2.2
                                  linarith only [hlam, p9952_0]
                              · linarith only [h9575, h9946, h9951, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h9575, h9933, h9938, h9950, hlam]
                      · linarith only [h8410, h8411, h9575, h9933, h9938, h9945, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                · linarith only [h0, h8410, h9575, h9933, h9940, hc24, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h8410, h9939, hc23, hlam, hphi, ht01, ht12, u0ehi2]
            · linarith only [h9575, h9933, h9938, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h9992 | h9992
        · linarith only [h0, h8410, h9575, h9992, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h9994 | h9994
          · linarith only [h0, h8410, h9933, h9994, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h9996 | h9996
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9997 | h9997
              · rcases m.htr 1 2 5 (by decide) (by decide) with h9998 | h9998
                · linarith only [h0, h9933, h9998, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h8410, h9998, hc25, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h8410, h9997, hc23, hlam, hphi, ht01, ht12, u0ehi2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10002 | h10002
              · rcases m.htr 1 2 5 (by decide) (by decide) with h10003 | h10003
                · linarith only [h0, h10003, h8410, h9933, hc12, hlam, hphi, ht01, u0ehi2]
                · linarith only [h0, h10003, h8410, hc25, hlam, hphi, ht01, ht12, u0ehi2]
              · linarith only [h0, h10002, h8410, hc23, hlam, hphi, ht01, ht12, u0ehi2]
  · linarith only [h0, h8410, h9574, hlam]

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h8411 | h8411
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0 m hb0 hb2 hb3 hb5 hg0 h8410 h8411
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x1 m hb0 hb2 hb3 hb5 hg0 h8410 h8411

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10 m hb0 hb2 hb3 hb5 h0 h8410

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h8410 | h8410
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0 m hb0 hb2 hb3 hb5 hg0 h8410
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x1 m hb0 hb2 hb3 hb5 hg0 h8410

set_option maxHeartbeats 27998000 in
set_option maxHeartbeats 27998000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9 m hb0 hb2 hb3 hb5 h0

end R2N4
