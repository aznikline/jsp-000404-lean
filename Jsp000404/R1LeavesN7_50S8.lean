import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h585 | h585
  · rcases m.htr 0 3 5 (by decide) (by decide) with h586 | h586
    · rcases m.htr 0 4 5 (by decide) (by decide) with h587 | h587
      · rcases m.htr 1 2 3 (by decide) (by decide) with h588 | h588
        · rcases m.htr 1 2 5 (by decide) (by decide) with h589 | h589
          · linarith only [h0, h3, h589, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
            · rcases m.htr 1 3 5 (by decide) (by decide) with h592 | h592
              · linarith only [h588, h589, h592, hlam]
              · linarith only [h591, h592, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h595 | h595
              · linarith only [h1, h585, h591, h595, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                · rcases m.htr 2 3 4 (by decide) (by decide) with h598 | h598
                  · linarith only [h588, h589, h591, h597, h598, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h600 | h600
                    · linarith only [h1, h585, h588, h589, h591, h595, h597, h600, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h3, h586, h600, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                  · linarith only [h587, h588, h591, h597, h603, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h605 | h605
                    · linarith only [h1, h585, h587, h588, h591, h597, h605, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h0, h3, h588, h605, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h608 | h608
          · linarith only [h0, h3, h608, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
            · rcases m.htr 1 3 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h614 | h614
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h615 | h615
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h616 | h616
                        · rcases h5bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h3, h608, h613, h615, hc12, hc23, hlam, hphi, p617_1]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h3, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h3, h613, h615, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p617_1, u3ehi4]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            rcases p617_3 (m.d 0 5) (by simp) with h622 | h622
                            · rcases p617_3 (m.d 1 5) (by simp) with h623 | h623
                              · linarith only [h2, h623, hlam]
                              · linarith only [h612, h623, hlam]
                            · linarith only [h587, h622, hlam]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h2, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h608, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p617_1, u3ehi4]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h1, h610, h612, hc01, hc45, hlam, hphi, ht0b, ht5b, p617_1]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h3, h613, h615, hc02, hc23, hlam, hphi, p617_1]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h608, h613, h615, hc12, hc23, hlam, hphi, p617_1]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h613, h615, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p617_1, u3ehi4]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            rcases p617_3 (m.d 0 5) (by simp) with h636 | h636
                            · linarith only [h3, h636, hlam]
                            · linarith only [h587, h636, hlam]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h586, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h611, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h614, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h2, h611, hc01, hc45, hlam, hphi, ht0b, ht5b, p617_1]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h587, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h612, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h615, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [h616, hlam, p617_0]
                          · have p617_0 := h617c.1
                            have p617_1 := h617c.2.1
                            have p617_2 := h617c.2.2.1
                            have p617_3 := h617c.2.2.2
                            linarith only [hlam, p617_0]
                        · linarith only [h1, h610, h612, h616, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h610, h612, h613, h615, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1, h611, h614, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h588, h611, h613, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h653 | h653
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h654 | h654
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h655 | h655
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h656 | h656
                        · linarith only [h610, h612, h656, hlam]
                        · rcases h5bigk with h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h3, h608, h653, h655, hc12, hc23, hlam, hphi, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h3, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h3, h653, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p658_1, u3ehi4]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h3, h612, h653, h655, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h2, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h608, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p658_1, u3ehi4]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h612, hlam, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h0, h3, h653, h655, hc12, hc23, hlam, hphi, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h608, h653, h655, hc12, hc23, hlam, hphi, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h653, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p658_1, u3ehi4]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h610, h612, h653, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p658_1, u3ehi3]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h586, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h611, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h654, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h656, hlam, p658_1]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h587, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h585, h587, h610, h612, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p658_1, u3ehi3]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h655, hlam, p658_0]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [h653, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p658_1, u3ehi4]
                          · have p658_0 := h658c.1
                            have p658_1 := h658c.2.1
                            have p658_2 := h658c.2.2.1
                            have p658_3 := h658c.2.2.2
                            linarith only [hlam, p658_0]
                      · linarith only [h3, h587, h655, hlam]
                    · linarith only [h588, h610, h654, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h588, h610, h653, hlam]
              · linarith only [h610, h611, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h688 | h688
              · linarith only [h1, h585, h610, h688, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h690 | h690
                · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                        · rcases h5bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h688, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1, u3ehi1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h3, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h3, h688, h691, h693, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p695_1, u3ehi1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            rcases p695_3 (m.d 0 5) (by simp) with h700 | h700
                            · rcases p695_3 (m.d 1 5) (by simp) with h701 | h701
                              · linarith only [h2, h701, hlam]
                              · linarith only [h690, h701, hlam]
                            · linarith only [h587, h700, hlam]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h2, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h608, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h688, hlam, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h3, h691, h693, hc02, hc23, hlam, hphi, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h608, h691, h693, hc12, hc23, hlam, hphi, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h688, h691, h693, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p695_1, u3ehi1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            rcases p695_3 (m.d 0 5) (by simp) with h714 | h714
                            · linarith only [h3, h714, hlam]
                            · linarith only [h587, h714, hlam]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h586, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h585, h688, h694, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1, u3ehi1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h692, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h691, h694, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p695_1]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h587, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h690, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h693, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [h694, hlam, p695_0]
                          · have p695_0 := h695c.1
                            have p695_1 := h695c.2.1
                            have p695_2 := h695c.2.2.1
                            have p695_3 := h695c.2.2.2
                            linarith only [hlam, p695_0]
                        · linarith only [h1, h585, h587, h610, h694, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h610, h690, h691, h693, hlam]
                    · linarith only [h691, h692, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h730 | h730
                    · linarith only [h691, h730, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h3, h586, h730, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h736 | h736
                        · linarith only [h610, h690, h733, h736, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h610, h735, h736, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h610, h733, h735, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h586, h610, h733, h734, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h741 | h741
                    · linarith only [h733, h741, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h3, h586, h741, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h744 | h744
        · rcases m.htr 1 2 5 (by decide) (by decide) with h745 | h745
          · linarith only [h0, h3, h745, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h747 | h747
            · rcases m.htr 1 3 5 (by decide) (by decide) with h748 | h748
              · linarith only [h744, h745, h748, hlam]
              · linarith only [h747, h748, hc35, hlam, hphi, u3ehi3]
            · linarith only [h585, h587, h747, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h752 | h752
          · linarith only [h0, h3, h752, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
            · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
              · rcases m.htr 1 4 5 (by decide) (by decide) with h756 | h756
                · linarith only [h1, h585, h587, h754, h756, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h758 | h758
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h760 | h760
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h761 | h761
                        · linarith only [h585, h587, h761, hlam]
                        · rcases h5bigk with h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h754, h756, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p763_1, u3ehi3]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h3, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p763_1, u3ehi4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h587, hlam, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h2, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h752, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p763_1, u3ehi4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h756, hlam, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h3, hc02, hc25, hlam, hphi, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h752, hc12, hc25, hlam, hphi, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h759, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p763_1, u3ehi4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h585, h587, h758, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p763_1, u3ehi3]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h586, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h755, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h759, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h761, hlam, p763_1]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h2, h754, h756, hc45, hlam, hphi, ht34, p763_1, u3ehi3]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h754, h756, hc45, hlam, hphi, ht34, p763_1, u3ehi3]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h760, hlam, p763_0]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [h758, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p763_1, u3ehi4]
                          · have p763_0 := h763c.1
                            have p763_1 := h763c.2.1
                            have p763_2 := h763c.2.2.1
                            have p763_3 := h763c.2.2.2
                            linarith only [hlam, p763_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                        · linarith only [h2, h3, h754, h756, h760, h789, hlam]
                        · rcases h5bigk with h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h587, h752, hc12, hc45, hlam, hphi, ht23, ht34, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h3, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h587, h789, hc45, hlam, hphi, ht34, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h587, hlam, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h2, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h752, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h789, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h756, hlam, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h0, h3, hc12, hc25, hlam, hphi, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h752, hc12, hc25, hlam, hphi, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h759, h789, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h760, hlam, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h586, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h755, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h759, hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [hlam, p791_0]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h789, hlam, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h2, h755, h789, hc45, hlam, hphi, ht34, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h755, h789, hc45, hlam, hphi, ht34, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h0, h3, hc12, hc45, hlam, hphi, ht23, ht34, p791_1]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [h789, hc45, hlam, hphi, ht34, p791_1, u3ehi3]
                          · have p791_0 := h791c.1
                            have p791_1 := h791c.2.1
                            have p791_2 := h791c.2.2.1
                            have p791_3 := h791c.2.2.2
                            linarith only [hlam, p791_0]
                    · linarith only [h744, h754, h759, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h744, h754, h758, hlam]
              · linarith only [h754, h755, hc35, hlam, hphi, u3ehi3]
            · linarith only [h585, h587, h754, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h585, h586, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h822 | h822
    · linarith only [h585, h822, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h824 | h824
      · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
        · rcases m.htr 1 2 5 (by decide) (by decide) with h826 | h826
          · linarith only [h0, h3, h826, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h828 | h828
            · linarith only [h1, h585, h828, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h830 | h830
              · linarith only [h1, h585, h830, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                  · linarith only [h0, h3, h585, h825, h833, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h835 | h835
                    · linarith only [h1, h585, h825, h835, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h3, h825, h835, hc35, hlam, hphi, u3ehi2]
                · linarith only [h585, h824, h828, h832, hc34, hlam, hphi, u3ehi1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
          · linarith only [h3, h825, h839, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h841 | h841
            · linarith only [h1, h585, h841, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h843 | h843
              · linarith only [h1, h585, h843, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h845 | h845
                · rcases m.htr 2 3 4 (by decide) (by decide) with h846 | h846
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h847 | h847
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h849 | h849
                        · rcases h5bigk with h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c | h850c
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h585, h824, h846, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h3, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h822, hlam, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h585, h824, h846, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h2, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h839, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h843, hlam, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h3, h846, h848, hc02, hc23, hlam, hphi, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h839, h846, h848, hc12, hc23, hlam, hphi, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h846, h848, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p850_1, u3ehi4]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            rcases p850_3 (m.d 0 5) (by simp) with h865 | h865
                            · linarith only [h3, h865, hlam]
                            · linarith only [h824, h865, hlam]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h1, h822, hc35, hlam, hphi, p850_1, u3ehi1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h843, hc35, hlam, hphi, p850_1, u3ehi1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h847, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h846, h849, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p850_1]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h824, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h845, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h848, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [h849, hlam, p850_0]
                          · have p850_0 := h850c.1
                            have p850_1 := h850c.2.1
                            have p850_2 := h850c.2.2.1
                            have p850_3 := h850c.2.2.2
                            linarith only [hlam, p850_0]
                        · linarith only [h1, h585, h849, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h585, h824, h846, h848, hlam]
                    · linarith only [h1, h585, h846, h847, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                    · linarith only [h846, h881, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h883 | h883
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h884 | h884
                        · rcases h5bigk with h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c | h885c
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h3, h839, h846, h883, hc12, hc34, hlam, hphi, ht23, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h3, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h822, hlam, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            rcases p885_3 (m.d 0 5) (by simp) with h890 | h890
                            · rcases p885_3 (m.d 1 5) (by simp) with h891 | h891
                              · linarith only [h2, h891, hlam]
                              · linarith only [h845, h891, hlam]
                            · linarith only [h824, h890, hlam]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h2, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h839, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h843, hlam, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h0, h3, h846, h883, hc12, hc34, hlam, hphi, ht23, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h839, h846, h883, hc12, hc34, hlam, hphi, ht23, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h881, hlam, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            rcases p885_3 (m.d 0 5) (by simp) with h904 | h904
                            · linarith only [h3, h904, hlam]
                            · linarith only [h824, h904, hlam]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h1, h822, h884, hc34, hlam, hphi, p885_1, u3ehi1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h843, h884, hc34, hlam, hphi, p885_1, u3ehi1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h0, h3, h884, hc12, hc34, hlam, hphi, ht23, p885_1]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            rcases p885_3 (m.d 0 5) (by simp) with h911 | h911
                            · linarith only [h822, h911, hlam]
                            · linarith only [h824, h911, hlam]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h824, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h845, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h883, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [h884, hlam, p885_0]
                          · have p885_0 := h885c.1
                            have p885_1 := h885c.2.1
                            have p885_2 := h885c.2.2.1
                            have p885_3 := h885c.2.2.2
                            linarith only [hlam, p885_0]
                        · linarith only [h1, h585, h884, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h585, h824, h846, h883, hc34, hlam, hphi, u3ehi2]
                · linarith only [h585, h824, h841, h845, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
        · rcases m.htr 1 2 5 (by decide) (by decide) with h923 | h923
          · linarith only [h0, h3, h923, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h925 | h925
            · linarith only [h1, h585, h925, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
              · linarith only [h1, h585, h824, h927, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                · linarith only [h585, h824, h925, h929, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h931 | h931
                  · linarith only [h0, h3, h922, h931, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h933 | h933
                    · linarith only [h2, h822, h922, h923, h933, hlam]
                    · linarith only [h0, h3, h922, h933, hc35, hlam, hphi, u3ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h936 | h936
          · linarith only [h3, h922, h936, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
            · linarith only [h1, h585, h938, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
              · linarith only [h1, h585, h824, h940, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h942 | h942
                · linarith only [h585, h824, h938, h942, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h946 | h946
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h947 | h947
                        · linarith only [h1, h585, h824, h947, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h585, h944, h946, h947, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h585, h944, h946, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h1, h585, h944, h945, hc35, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h952 | h952
                    · linarith only [h944, h952, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                      · linarith only [h1, h585, h824, h944, h954, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                        · linarith only [h1, h585, h824, h956, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h585, h956, hc45, hlam, hphi, ht34, u3ehi1]

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h959 | h959
  · linarith only [h0, h2, h959, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h961 | h961
    · rcases m.htr 0 3 5 (by decide) (by decide) with h962 | h962
      · linarith only [h1, h2, h962, hlam]
      · linarith only [h961, h962, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h965 | h965
      · linarith only [h961, h965, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
        · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
          · linarith only [h0, h2, h968, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h970 | h970
            · linarith only [h1, h2, h959, h968, h970, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
              · linarith only [h1, h2, h961, h970, h972, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h974 | h974
                · linarith only [h1, h2, h965, h974, hlam]
                · linarith only [h1, h2, h974, hc35, hlam, hphi, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
          · linarith only [h0, h2, h977, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
            · linarith only [h0, h959, h979, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
              · linarith only [h1, h961, h981, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h983 | h983
                · linarith only [h1, h961, h983, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1, h2, h983, hc35, hlam, hphi, u3ehi1]

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2

end R2N4
