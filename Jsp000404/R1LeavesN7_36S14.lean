import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h586 | h586
  · rcases m.htr 0 2 5 (by decide) (by decide) with h587 | h587
    · rcases m.htr 0 3 4 (by decide) (by decide) with h588 | h588
      · rcases m.htr 0 3 5 (by decide) (by decide) with h589 | h589
        · rcases m.htr 0 4 5 (by decide) (by decide) with h590 | h590
          · rcases m.htr 1 4 5 (by decide) (by decide) with h591 | h591
            · rcases m.htr 3 4 5 (by decide) (by decide) with h592 | h592
              · rcases h0bigk with h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h2, h586, h591, hc01, hlam, hphi, ht0b, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h588, h592, hc01, hlam, hphi, ht0b, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h2, h591, hc01, hlam, hphi, ht0b, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h590, hc01, hlam, hphi, ht0b, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h0, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h4, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h2, h4, h591, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p593_1]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h1, hlam, p593_1]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p593_1]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h2, h4, h591, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h4, h590, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h2, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h586, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h588, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h586, h590, hc02, hlam, hphi, ht0b, ht45, ht5b, p593_1, u4ehi4]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h3, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h587, hlam, p593_1]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h589, hlam, p593_0]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [h590, hlam, p593_1]
                · have p593_0 := h593c.1
                  have p593_1 := h593c.2.1
                  have p593_2 := h593c.2.2.1
                  have p593_3 := h593c.2.2.2
                  linarith only [hlam, p593_0]
              · linarith only [h2, h591, h592, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h4, h586, h590, h591, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
            · linarith only [h2, h590, h621, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h623 | h623
              · linarith only [h588, h590, h623, hlam]
              · rcases h0bigk with h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h586, hc01, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi2]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, h586, hc01, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi2]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h588, h590, hc01, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi3]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h0, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h588, hc02, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi3]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p625_1]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h1, hlam, p625_1]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, hc02, hc23, hlam, hphi, p625_1]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, h588, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi3]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h4, h588, h590, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi3]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h2, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h586, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h588, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h590, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h3, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h587, hlam, p625_1]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h589, hlam, p625_0]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [h588, hc05, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi3]
                · have p625_0 := h625c.1
                  have p625_1 := h625c.2.1
                  have p625_2 := h625c.2.2.1
                  have p625_3 := h625c.2.2.2
                  linarith only [hlam, p625_0]
        · linarith only [h4, h587, h589, hlam]
      · linarith only [h4, h586, h588, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h653 | h653
      · rcases m.htr 0 3 5 (by decide) (by decide) with h654 | h654
        · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
          · linarith only [h586, h587, h655, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
            · linarith only [h2, h655, h657, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h659 | h659
              · linarith only [h586, h587, h653, h655, h659, hlam]
              · rcases h0bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h586, hc01, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi2]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h654, h659, hc01, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi3]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h3, h657, hc01, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h0, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h4, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h2, hc02, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h587, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h1, hlam, p661_1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p661_1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p661_1, u4ehi1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h4, h586, h587, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p661_1, u4ehi2]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h2, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h586, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h653, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h655, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h3, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h586, hc05, hlam, hphi, ht0b, ht45, ht5b, p661_1, u4ehi2]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h654, hlam, p661_0]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [h2, h655, hc45, hlam, hphi, p661_1, u4ehi1]
                · have p661_0 := h661c.1
                  have p661_1 := h661c.2.1
                  have p661_2 := h661c.2.2.1
                  have p661_3 := h661c.2.2.2
                  linarith only [hlam, p661_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h687 | h687
          · linarith only [h586, h587, h687, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h689 | h689
            · linarith only [h2, h687, h689, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h691 | h691
              · linarith only [h653, h654, h687, h691, hlam]
              · linarith only [h4, h586, h654, h691, hc45, hlam, hphi, u4ehi2]
      · linarith only [h4, h586, h653, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h695 | h695
    · rcases m.htr 0 3 4 (by decide) (by decide) with h696 | h696
      · rcases m.htr 0 3 5 (by decide) (by decide) with h697 | h697
        · rcases m.htr 0 4 5 (by decide) (by decide) with h698 | h698
          · rcases m.htr 1 4 5 (by decide) (by decide) with h699 | h699
            · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
              · rcases h0bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h695, hc01, hc25, hlam, hphi, ht0b, ht5b, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h696, h700, hc01, hlam, hphi, ht0b, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h2, h699, hc01, hlam, hphi, ht0b, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, h699, hc01, hlam, hphi, ht0b, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h0, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h4, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h586, hlam, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, h699, hc02, hlam, hphi, ht0b, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h1, hlam, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h2, h4, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, h4, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h2, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, h695, h699, hc04, hlam, hphi, ht0b, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h696, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, h4, h696, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p701_1, u4ehi4]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h3, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h695, hlam, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h697, hlam, p701_0]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [h698, hlam, p701_1]
                · have p701_0 := h701c.1
                  have p701_1 := h701c.2.1
                  have p701_2 := h701c.2.2.1
                  have p701_3 := h701c.2.2.2
                  linarith only [hlam, p701_0]
              · linarith only [h2, h699, h700, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h728 | h728
              · linarith only [h4, h696, h699, h728, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases h0bigk with h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c | h730c
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h695, h698, h699, hc01, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h696, hc01, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h698, h699, hc01, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h0, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h4, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h586, hlam, p730_1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h698, h699, hc02, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h1, hlam, p730_1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p730_1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h4, h586, h695, h698, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h4, h698, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h2, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h695, h698, h699, hc04, hlam, hphi, ht0b, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h696, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h4, h696, h698, h699, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p730_1, u4ehi1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h3, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h695, hlam, p730_1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h697, hlam, p730_0]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [h698, hlam, p730_1]
                · have p730_0 := h730c.1
                  have p730_1 := h730c.2.1
                  have p730_2 := h730c.2.2.1
                  have p730_3 := h730c.2.2.2
                  linarith only [hlam, p730_0]
          · linarith only [h586, h695, h698, hlam]
        · linarith only [h4, h695, h697, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
        · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
          · rcases m.htr 1 4 5 (by decide) (by decide) with h760 | h760
            · rcases m.htr 3 4 5 (by decide) (by decide) with h761 | h761
              · rcases h0bigk with h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h695, hc01, hc25, hlam, hphi, ht0b, ht5b, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h758, h761, hc01, hlam, hphi, ht0b, ht45, ht5b, p762_1, u4ehi4]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h696, h758, h761, hc01, hlam, hphi, ht0b, ht45, ht5b, p762_1, u4ehi4]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h758, h761, hc01, hlam, hphi, ht0b, ht45, ht5b, p762_1, u4ehi4]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h0, hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h4, hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h586, hlam, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h1, hlam, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h696, hc02, hc34, hlam, hphi, ht23, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h696, hlam, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h3, h696, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h2, hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h695, hc04, hc25, hlam, hphi, ht0b, ht5b, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h696, h758, h761, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p762_1, u4ehi4]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h696, h758, h761, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p762_1, u4ehi4]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h3, hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h695, hlam, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h758, hlam, p762_0]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [h759, hlam, p762_1]
                · have p762_0 := h762c.1
                  have p762_1 := h762c.2.1
                  have p762_2 := h762c.2.2.1
                  have p762_3 := h762c.2.2.2
                  linarith only [hlam, p762_0]
              · linarith only [h696, h759, h761, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
              · linarith only [h696, h758, h760, h789, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h4, h695, h696, h758, h759, h789, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · linarith only [h586, h695, h759, hlam]
        · linarith only [h4, h695, h758, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h794 | h794
      · rcases m.htr 0 3 5 (by decide) (by decide) with h795 | h795
        · rcases m.htr 0 4 5 (by decide) (by decide) with h796 | h796
          · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
            · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
              · rcases h0bigk with h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c | h799c
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  rcases p799_3 (m.d 0 1) (by simp) with h801 | h801
                  · rcases p799_3 (m.d 0 2) (by simp) with h802 | h802
                    · linarith only [h0, h802, hlam]
                    · rcases p799_3 (m.d 0 3) (by simp) with h804 | h804
                      · linarith only [h1, h804, hlam]
                      · linarith only [h4, h804, hlam]
                  · linarith only [h0, h801, hlam]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h794, h798, hc01, hlam, hphi, ht0b, ht45, ht5b, p799_1, u4ehi4]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h2, h797, hc01, hlam, hphi, ht0b, ht45, ht5b, p799_1, u4ehi4]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h796, hc01, hlam, hphi, ht0b, ht45, ht5b, p799_1, u4ehi4]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h4, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h586, hlam, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h695, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h1, hlam, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h2, h4, h797, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p799_1, u4ehi4]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, h4, h695, hc12, hc23, hlam, hphi, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h2, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, h586, hc12, hc24, hlam, hphi, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h794, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, h4, h695, h794, hc12, hc23, hlam, hphi, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h3, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h795, hlam, p799_0]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [h796, hlam, p799_1]
                · have p799_0 := h799c.1
                  have p799_1 := h799c.2.1
                  have p799_2 := h799c.2.2.1
                  have p799_3 := h799c.2.2.2
                  linarith only [hlam, p799_0]
              · linarith only [h2, h797, h798, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
              · linarith only [h4, h794, h797, h832, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases h0bigk with h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  rcases p834_3 (m.d 0 1) (by simp) with h836 | h836
                  · rcases p834_3 (m.d 0 2) (by simp) with h837 | h837
                    · linarith only [h0, h837, hlam]
                    · rcases p834_3 (m.d 0 3) (by simp) with h839 | h839
                      · linarith only [h1, h839, hlam]
                      · linarith only [h4, h839, hlam]
                  · linarith only [h0, h836, hlam]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h794, hc01, hlam, hphi, ht0b, ht45, ht5b, p834_1, u4ehi0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p834_1, u4ehi0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h796, h797, hc01, hlam, hphi, ht0b, ht45, ht5b, p834_1, u4ehi1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h4, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h586, hlam, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h695, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h1, hlam, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h4, h796, h797, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p834_1, u4ehi1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, h4, h695, hc12, hc23, hlam, hphi, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h2, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, h586, hc12, hc24, hlam, hphi, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h794, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, h4, h695, h794, hc12, hc23, hlam, hphi, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h3, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h795, hlam, p834_0]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [h796, hlam, p834_1]
                · have p834_0 := h834c.1
                  have p834_1 := h834c.2.1
                  have p834_2 := h834c.2.2.1
                  have p834_3 := h834c.2.2.2
                  linarith only [hlam, p834_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h866 | h866
            · linarith only [h2, h796, h866, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h868 | h868
              · linarith only [h2, h4, h794, h796, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases h0bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  rcases p870_3 (m.d 0 1) (by simp) with h872 | h872
                  · rcases p870_3 (m.d 0 2) (by simp) with h873 | h873
                    · linarith only [h0, h873, hlam]
                    · rcases p870_3 (m.d 0 3) (by simp) with h875 | h875
                      · linarith only [h1, h875, hlam]
                      · linarith only [h4, h875, hlam]
                  · linarith only [h0, h872, hlam]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h794, hc01, hlam, hphi, ht0b, ht45, ht5b, p870_1, u4ehi3]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p870_1, u4ehi1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, h796, hc01, hlam, hphi, ht0b, ht45, ht5b, p870_1, u4ehi1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h4, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h586, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h695, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h1, hlam, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p870_1, u4ehi1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h4, h695, hc12, hc23, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h2, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h796, hc12, hc45, hlam, hphi, ht23, ht34, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h794, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h796, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h3, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p870_1]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h795, hlam, p870_0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [h796, hc45, hlam, hphi, p870_1, u4ehi0]
                · have p870_0 := h870c.1
                  have p870_1 := h870c.2.1
                  have p870_2 := h870c.2.2.1
                  have p870_3 := h870c.2.2.2
                  linarith only [hlam, p870_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h902 | h902
          · linarith only [h794, h795, h902, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h904 | h904
            · linarith only [h2, h794, h795, h902, h904, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h906 | h906
              · linarith only [h794, h902, h906, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h794, h795, h906, hc45, hlam, hphi, u4ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h909 | h909
        · rcases m.htr 0 4 5 (by decide) (by decide) with h910 | h910
          · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
            · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
              · rcases h0bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  rcases p913_3 (m.d 0 1) (by simp) with h915 | h915
                  · rcases p913_3 (m.d 0 2) (by simp) with h916 | h916
                    · linarith only [h0, h916, hlam]
                    · rcases p913_3 (m.d 0 3) (by simp) with h918 | h918
                      · linarith only [h1, h918, hlam]
                      · linarith only [h4, h918, hlam]
                  · linarith only [h0, h915, hlam]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h909, h912, hc01, hlam, hphi, ht0b, ht45, ht5b, p913_1, u4ehi4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h794, h909, h912, hc01, hlam, hphi, ht0b, ht45, ht5b, p913_1, u4ehi4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h909, h912, hc01, hlam, hphi, ht0b, ht45, ht5b, p913_1, u4ehi4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h4, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h586, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h695, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h1, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, h794, hc12, hc34, hlam, hphi, ht23, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h794, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h794, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h2, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, h586, hc12, hc24, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h794, h909, h912, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p913_1, u4ehi4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h794, h909, h912, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p913_1, u4ehi4]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h3, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h909, hlam, p913_0]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [h910, hlam, p913_1]
                · have p913_0 := h913c.1
                  have p913_1 := h913c.2.1
                  have p913_2 := h913c.2.2.1
                  have p913_3 := h913c.2.2.2
                  linarith only [hlam, p913_0]
              · linarith only [h2, h794, h911, h912, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
              · linarith only [h794, h909, h911, h946, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h794, h910, h946, hlam]
          · linarith only [h794, h909, h910, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h950 | h950
          · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
            · rcases m.htr 3 4 5 (by decide) (by decide) with h952 | h952
              · rcases h0bigk with h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  rcases p953_3 (m.d 0 1) (by simp) with h955 | h955
                  · rcases p953_3 (m.d 0 2) (by simp) with h956 | h956
                    · linarith only [h0, h956, hlam]
                    · rcases p953_3 (m.d 0 3) (by simp) with h958 | h958
                      · linarith only [h1, h958, hlam]
                      · linarith only [h4, h958, hlam]
                  · linarith only [h0, h955, hlam]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  rcases p953_3 (m.d 0 1) (by simp) with h962 | h962
                  · rcases p953_3 (m.d 0 2) (by simp) with h963 | h963
                    · linarith only [h0, h963, hlam]
                    · rcases p953_3 (m.d 0 3) (by simp) with h965 | h965
                      · linarith only [h1, h965, hlam]
                      · rcases p953_3 (m.d 0 4) (by simp) with h967 | h967
                        · linarith only [h2, h967, hlam]
                        · linarith only [h794, h967, hlam]
                  · linarith only [h1, h962, hlam]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h2, h951, hc01, hlam, hphi, ht0b, ht45, ht5b, p953_1, u4ehi4]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h950, hc01, hlam, hphi, ht0b, ht45, ht5b, p953_1, u4ehi4]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h4, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h586, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h695, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h1, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, h909, hc12, hc35, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h794, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h909, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h2, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, h586, hc12, hc24, hlam, hphi, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h794, hc03, hc34, hlam, hphi, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, h4, h794, h909, hc12, hc34, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h3, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, h4, h909, hc12, hc35, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h950, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
              · linarith only [h2, h794, h951, h952, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h994 | h994
              · rcases h0bigk with h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c | h995c
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  rcases p995_3 (m.d 0 1) (by simp) with h997 | h997
                  · rcases p995_3 (m.d 0 2) (by simp) with h998 | h998
                    · linarith only [h0, h998, hlam]
                    · rcases p995_3 (m.d 0 3) (by simp) with h1000 | h1000
                      · linarith only [h1, h1000, hlam]
                      · linarith only [h1000, h4, hlam]
                  · linarith only [h0, h997, hlam]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  rcases p995_3 (m.d 0 1) (by simp) with h1004 | h1004
                  · rcases p995_3 (m.d 0 2) (by simp) with h1005 | h1005
                    · linarith only [h0, h1005, hlam]
                    · rcases p995_3 (m.d 0 3) (by simp) with h1007 | h1007
                      · linarith only [h1, h1007, hlam]
                      · rcases p995_3 (m.d 0 4) (by simp) with h1009 | h1009
                        · linarith only [h1009, h2, hlam]
                        · linarith only [h1009, h794, hlam]
                  · linarith only [h1, h1004, hlam]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h950, h951, hc01, hlam, hphi, ht0b, ht45, ht5b, p995_1, u4ehi1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h950, h951, hc01, hlam, hphi, ht0b, ht45, ht5b, p995_1, u4ehi1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h4, hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h586, hlam, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h695, hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h1, hlam, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h794, hlam, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h909, hlam, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h2, hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, h794, hc12, hc34, hlam, hphi, ht23, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h794, hc03, hc34, hlam, hphi, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, h695, h794, hc12, hc34, hlam, hphi, ht23, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h3, hlam, p995_0]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h0, h4, h909, h994, hc12, hc34, hlam, hphi, ht23, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [h950, hlam, p995_1]
                · have p995_0 := h995c.1
                  have p995_1 := h995c.2.1
                  have p995_2 := h995c.2.2.1
                  have p995_3 := h995c.2.2.2
                  linarith only [hlam, p995_0]
              · linarith only [h794, h950, h994, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
            · linarith only [h1036, h2, h950, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1038 | h1038
              · rcases h0bigk with h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  rcases p1039_3 (m.d 0 1) (by simp) with h1041 | h1041
                  · rcases p1039_3 (m.d 0 2) (by simp) with h1042 | h1042
                    · linarith only [h0, h1042, hlam]
                    · rcases p1039_3 (m.d 0 3) (by simp) with h1044 | h1044
                      · linarith only [h1, h1044, hlam]
                      · linarith only [h1044, h4, hlam]
                  · linarith only [h0, h1041, hlam]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  rcases p1039_3 (m.d 0 1) (by simp) with h1048 | h1048
                  · rcases p1039_3 (m.d 0 2) (by simp) with h1049 | h1049
                    · linarith only [h0, h1049, hlam]
                    · rcases p1039_3 (m.d 0 3) (by simp) with h1051 | h1051
                      · linarith only [h1, h1051, hlam]
                      · rcases p1039_3 (m.d 0 4) (by simp) with h1053 | h1053
                        · linarith only [h1053, h2, hlam]
                        · linarith only [h1053, h794, hlam]
                  · linarith only [h1, h1048, hlam]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1039_1, u4ehi1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h1036, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1039_1, u4ehi1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h0, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h4, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h586, hlam, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h695, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h1, hlam, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h794, hlam, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h909, hlam, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h2, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h0, h1038, h950, hc12, hc34, hlam, hphi, ht23, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h1038, h950, hc03, hc34, hlam, hphi, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h950, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h3, hlam, p1039_0]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h0, h4, h909, hc12, hc35, hlam, hphi, ht23, p1039_1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [h1038, h2, h950, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1039_1, u4ehi1]
                · have p1039_0 := h1039c.1
                  have p1039_1 := h1039c.2.1
                  have p1039_2 := h1039c.2.2.1
                  have p1039_3 := h1039c.2.2.2
                  linarith only [hlam, p1039_0]
              · rcases h0bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  rcases p1079_3 (m.d 0 1) (by simp) with h1081 | h1081
                  · rcases p1079_3 (m.d 0 2) (by simp) with h1082 | h1082
                    · linarith only [h0, h1082, hlam]
                    · rcases p1079_3 (m.d 0 3) (by simp) with h1084 | h1084
                      · linarith only [h1, h1084, hlam]
                      · linarith only [h1084, h4, hlam]
                  · linarith only [h0, h1081, hlam]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  rcases p1079_3 (m.d 0 1) (by simp) with h1088 | h1088
                  · rcases p1079_3 (m.d 0 2) (by simp) with h1089 | h1089
                    · linarith only [h0, h1089, hlam]
                    · rcases p1079_3 (m.d 0 3) (by simp) with h1091 | h1091
                      · linarith only [h1, h1091, hlam]
                      · rcases p1079_3 (m.d 0 4) (by simp) with h1093 | h1093
                        · linarith only [h1093, h2, hlam]
                        · linarith only [h1093, h794, hlam]
                  · linarith only [h1, h1088, hlam]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1079_1, u4ehi1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h1036, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p1079_1, u4ehi1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h0, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h4, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h586, hlam, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h695, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h1, hlam, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h794, hlam, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h909, hlam, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h2, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h0, h586, hc12, hc24, hlam, hphi, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h1038, h794, hc03, hc45, hlam, hphi, ht34, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h950, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h3, hlam, p1079_0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h0, h695, hc12, hc25, hlam, hphi, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h0, h1038, h4, h909, hc12, hc45, hlam, hphi, ht23, ht34, p1079_1]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [h1038, h909, hc45, hlam, hphi, p1079_1, u4ehi0]
                · have p1079_0 := h1079c.1
                  have p1079_1 := h1079c.2.1
                  have p1079_2 := h1079c.2.2.1
                  have p1079_3 := h1079c.2.2.2
                  linarith only [hlam, p1079_0]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1119 | h1119
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1120 | h1120
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1121 | h1121
      · linarith only [h0, h1121, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1123 | h1123
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1124 | h1124
          · linarith only [h0, h1119, h1124, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1126 | h1126
            · linarith only [h0, h1119, h1123, h1126, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
              · linarith only [h1126, h1128, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1128, h2, h3, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1131 | h1131
          · linarith only [h0, h1120, h1123, h1131, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
            · linarith only [h0, h1120, h1133, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1135 | h1135
              · linarith only [h1133, h1135, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1135, h2, h3, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1138 | h1138
      · linarith only [h1120, h1138, h2, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1140 | h1140
        · linarith only [h1119, h1120, h1140, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1142 | h1142
          · linarith only [h1119, h1120, h1142, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1144 | h1144
            · linarith only [h1144, h2, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1146 | h1146
              · linarith only [h1144, h1146, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1146, h2, h3, hc45, hlam, hphi, u4ehi1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1149 | h1149
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1150 | h1150
      · linarith only [h1, h1119, h1150, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1152 | h1152
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1153 | h1153
          · linarith only [h1, h1153, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1155 | h1155
            · linarith only [h1, h1119, h1149, h1155, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1157 | h1157
              · linarith only [h1155, h1157, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1157, h2, h3, hc45, hlam, hphi, u4ehi1]
        · linarith only [h1119, h1149, h1152, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1161 | h1161
      · linarith only [h0, h1161, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1163 | h1163
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1164 | h1164
          · linarith only [h1, h1164, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
            · linarith only [h1, h1163, h1166, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1168 | h1168
              · linarith only [h1166, h1168, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1168, h2, h3, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1171 | h1171
          · linarith only [h1, h1171, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1173 | h1173
            · linarith only [h1173, h2, h3, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1175 | h1175
              · linarith only [h1173, h1175, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h1175, h2, h3, hc45, hlam, hphi, u4ehi1]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3

end R2N4
