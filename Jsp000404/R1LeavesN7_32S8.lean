import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3689 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h3690 | h3690
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3691 | h3691
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3692 | h3692
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3693 | h3693
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3694 | h3694
          · linarith only [h3145, h3689, h3693, h3694, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3696 | h3696
            · rcases h0bigk with h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h0, hlam, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2352, hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2875, hlam, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2994, hlam, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3145, hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hc02, hlam, hphi, ht0b, ht45, ht5b, p3697_1, u4ehi0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3145, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2352, h3694, hc01, hc23, hlam, hphi, ht12, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2352, h3694, hc02, hc23, hlam, hphi, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2352, h3693, h3694, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3697_1, u4ehi4]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2352, h2994, h3694, hc01, hc23, hlam, hphi, ht12, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h0, h3689, hc01, hc12, hlam, hphi, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3689, hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3691, hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2994, h3145, h3689, hc01, hc23, hlam, hphi, ht12, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h2994, h3696, hc01, hc14, hlam, hphi, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3690, hlam, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3692, hlam, p3697_0]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [h3693, hlam, p3697_1]
              · have p3697_0 := h3697c.1
                have p3697_1 := h3697c.2.1
                have p3697_2 := h3697c.2.2.1
                have p3697_3 := h3697c.2.2.2
                linarith only [hlam, p3697_0]
            · linarith only [h2875, h3693, h3696, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3724 | h3724
          · linarith only [h3145, h3689, h3724, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3726 | h3726
            · rcases h0bigk with h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c | h3727c
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h0, hlam, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2352, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2875, hlam, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2994, hlam, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3145, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h0, h3724, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3727_1, u4ehi0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h0, h3724, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3145, hc01, hc23, hlam, hphi, ht12, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3145, hc02, hc23, hlam, hphi, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3145, h3691, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3727_1, u4ehi3]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2994, h3145, hc01, hc23, hlam, hphi, ht12, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2875, hc01, hc14, hlam, hphi, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3689, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3691, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3693, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h2994, h3726, hc01, hc14, hlam, hphi, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3690, hlam, p3727_1]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3692, hlam, p3727_0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [h3690, hc02, hlam, hphi, ht0b, ht45, ht5b, p3727_1, u4ehi0]
              · have p3727_0 := h3727c.1
                have p3727_1 := h3727c.2.1
                have p3727_2 := h3727c.2.2.1
                have p3727_3 := h3727c.2.2.2
                linarith only [hlam, p3727_0]
            · rcases h0bigk with h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c | h3753c
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h0, hlam, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2352, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2875, hlam, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2994, hlam, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h0, h3724, hc01, hc23, hlam, hphi, ht12, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3145, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h0, h3689, h3724, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3753_1, u4ehi2]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h0, h3724, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2352, h3724, hc01, hc23, hlam, hphi, ht12, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2352, h3724, hc02, hc23, hlam, hphi, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2352, h3689, h3724, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3753_1, u4ehi2]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2352, h2994, h3724, hc01, hc23, hlam, hphi, ht12, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2875, hc01, hc14, hlam, hphi, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3689, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3691, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3693, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h2994, hc01, hc15, hlam, hphi, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3690, hlam, p3753_1]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h3692, hlam, p3753_0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [h0, h3690, h3724, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3753_1, u4ehi0]
              · have p3753_0 := h3753c.1
                have p3753_1 := h3753c.2.1
                have p3753_2 := h3753c.2.2.1
                have p3753_3 := h3753c.2.2.2
                linarith only [hlam, p3753_0]
      · linarith only [h3145, h3690, h3692, hlam]
    · linarith only [h3145, h3689, h3691, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3781 | h3781
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3782 | h3782
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3783 | h3783
        · linarith only [h3689, h3690, h3783, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3785 | h3785
          · linarith only [h3145, h3689, h3785, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3787 | h3787
            · rcases h0bigk with h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c | h3788c
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h0, hlam, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2352, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2875, hlam, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2994, hlam, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3690, hc01, hc25, hlam, hphi, ht12, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3145, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h0, h3785, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3788_1, u4ehi0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3690, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2352, hc01, hc13, hlam, hphi, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3145, hc02, hc23, hlam, hphi, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3145, h3689, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3788_1, u4ehi2]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3145, h3689, h3690, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3788_1, u4ehi2]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2875, hc01, hc14, hlam, hphi, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3689, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3781, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3783, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2994, h3787, hc01, hc14, hlam, hphi, p3788_1]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h2994, h3689, h3787, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3788_1, u4ehi2]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3782, hlam, p3788_0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [h3783, hc45, hlam, hphi, p3788_1, u4ehi0]
              · have p3788_0 := h3788c.1
                have p3788_1 := h3788c.2.1
                have p3788_2 := h3788c.2.2.1
                have p3788_3 := h3788c.2.2.2
                linarith only [hlam, p3788_0]
            · rcases h0bigk with h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h0, hlam, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2352, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2875, hlam, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2994, hlam, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h0, h3785, hc01, hc23, hlam, hphi, ht12, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3145, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h0, h3689, h3785, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3814_1, u4ehi2]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3690, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2352, h3785, hc01, hc23, hlam, hphi, ht12, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2352, h3785, hc02, hc23, hlam, hphi, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2352, h3689, h3785, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3814_1, u4ehi2]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2352, h2994, h3785, hc01, hc23, hlam, hphi, ht12, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2875, h3787, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3689, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3781, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3783, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2994, h3787, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3814_1]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2994, h3689, h3787, hc45, hlam, hphi, p3814_1, u4ehi2]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h3782, hlam, p3814_0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [h2994, h3787, hc45, hlam, hphi, p3814_1, u4ehi0]
              · have p3814_0 := h3814c.1
                have p3814_1 := h3814c.2.1
                have p3814_2 := h3814c.2.2.1
                have p3814_3 := h3814c.2.2.2
                linarith only [hlam, p3814_0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3840 | h3840
        · linarith only [h3689, h3690, h3840, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3842 | h3842
          · linarith only [h3145, h3689, h3842, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3844 | h3844
            · rcases h0bigk with h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c | h3845c
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h0, hlam, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2352, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2875, hlam, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2994, hlam, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h0, hc01, hc12, hlam, hphi, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3145, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h0, h3842, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3845_1, u4ehi0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3690, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2352, hc01, hc13, hlam, hphi, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h0, h2994, h3782, hc01, hc15, hlam, hphi, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3689, h3690, h3782, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3845_1, u4ehi2]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3782, hlam, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2875, hc01, hc14, hlam, hphi, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3689, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3781, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3840, hlam, p3845_0]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3690, hc01, hc25, hlam, hphi, ht12, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3690, hc02, hc25, hlam, hphi, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h2352, h3690, hc01, hc25, hlam, hphi, ht12, p3845_1]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [h3689, h3840, h3844, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3845_1, u4ehi2]
              · have p3845_0 := h3845c.1
                have p3845_1 := h3845c.2.1
                have p3845_2 := h3845c.2.2.1
                have p3845_3 := h3845c.2.2.2
                linarith only [hlam, p3845_0]
            · rcases h0bigk with h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c | h3871c
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h0, hlam, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2352, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2875, hlam, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2994, hlam, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h0, h3842, hc01, hc23, hlam, hphi, ht12, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3145, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h0, h3689, h3842, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3871_1, u4ehi2]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3690, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2352, h3842, hc01, hc23, hlam, hphi, ht12, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2352, h3842, hc02, hc23, hlam, hphi, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2352, h3689, h3842, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3871_1, u4ehi2]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3782, hlam, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2875, hc01, hc14, hlam, hphi, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3689, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3781, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3840, hlam, p3871_0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h2994, hc01, hc15, hlam, hphi, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3689, h3690, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3871_1, u4ehi2]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3782, hc03, hc35, hlam, hphi, p3871_1]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [h3840, hc45, hlam, hphi, p3871_1, u4ehi0]
              · have p3871_0 := h3871c.1
                have p3871_1 := h3871c.2.1
                have p3871_2 := h3871c.2.2.1
                have p3871_3 := h3871c.2.2.2
                linarith only [hlam, p3871_0]
    · linarith only [h3145, h3689, h3781, hlam]

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3689 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3898 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h3899 | h3899
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3900 | h3900
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3901 | h3901
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3902 | h3902
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3903 | h3903
          · rcases h0bigk with h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c | h3904c
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h0, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2352, hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2875, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2994, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3145, h3902, hc01, hc12, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3145, hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3689, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3145, h3902, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2352, hc01, hc13, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3145, h3902, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3145, h3902, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3904_1, u4ehi0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2994, h3145, h3902, hc01, hc12, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3689, h3898, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3899, hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2994, h3145, h3899, h3902, hc01, hc12, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h2994, h3903, hc01, hc14, hlam, hphi, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3898, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3900, hlam, p3904_0]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [h3901, hlam, p3904_1]
            · have p3904_0 := h3904c.1
              have p3904_1 := h3904c.2.1
              have p3904_2 := h3904c.2.2.1
              have p3904_3 := h3904c.2.2.2
              linarith only [hlam, p3904_0]
          · linarith only [h2875, h3145, h3898, h3901, h3902, h3903, hc01, hc12, hlam, hphi]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3931 | h3931
          · rcases h0bigk with h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h0, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2875, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2994, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h0, h3902, hc01, hc23, hlam, hphi, ht12, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3145, hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3689, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h0, h3902, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, h3902, hc01, hc23, hlam, hphi, ht12, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, h3902, hc02, hc23, hlam, hphi, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, h3901, h3902, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3932_1, u4ehi4]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, h2994, h3902, hc01, hc23, hlam, hphi, ht12, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3689, h3898, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3899, hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2352, h2994, h3899, h3902, hc01, hc23, hlam, hphi, ht12, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h2994, h3931, hc01, hc14, hlam, hphi, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3898, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3900, hlam, p3932_0]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [h3901, hlam, p3932_1]
            · have p3932_0 := h3932c.1
              have p3932_1 := h3932c.2.1
              have p3932_2 := h3932c.2.2.1
              have p3932_3 := h3932c.2.2.2
              linarith only [hlam, p3932_0]
          · linarith only [h0, h2875, h3898, h3901, h3902, h3931, hc01, hc23, hlam, hphi, ht12]
      · linarith only [h3689, h3898, h3901, hlam]
    · linarith only [h3145, h3898, h3900, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3961 | h3961
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3962 | h3962
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3963 | h3963
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3964 | h3964
          · rcases h0bigk with h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c | h3965c
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h0, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h2352, hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h2875, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h2994, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3145, h3963, hc01, hc12, hlam, hphi, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3145, hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3689, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3145, h3963, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, hc01, hc34, hlam, hphi, ht12, ht23, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, hc02, hc34, hlam, hphi, ht23, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, h3962, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3965_1, u4ehi4]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3689, h3898, h3962, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3965_1, u4ehi4]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, hc03, hc34, hlam, hphi, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3899, h3962, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3965_1, u4ehi4]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h0, h3898, hc01, hc12, hlam, hphi, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3898, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3961, hlam, p3965_0]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [h3962, hlam, p3965_1]
            · have p3965_0 := h3965c.1
              have p3965_1 := h3965c.2.1
              have p3965_2 := h3965c.2.2.1
              have p3965_3 := h3965c.2.2.2
              linarith only [hlam, p3965_0]
          · linarith only [h2875, h3962, h3964, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3992 | h3992
          · rcases h0bigk with h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c | h3993c
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h0, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2352, hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2875, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2994, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h0, hc01, hc12, hlam, hphi, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3145, hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3689, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2352, h2994, h3145, h3963, hc01, hc23, hlam, hphi, ht12, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2352, h3963, hc01, hc23, hlam, hphi, ht12, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2352, h3963, hc02, hc23, hlam, hphi, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3899, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2994, h3899, hc01, hc34, hlam, hphi, ht12, ht23, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2875, hc01, hc14, hlam, hphi, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3689, h3898, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3899, hc03, hc34, hlam, hphi, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2994, h3899, hc01, hc34, hlam, hphi, ht12, ht23, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h2994, hc01, hc15, hlam, hphi, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3898, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3961, hlam, p3993_0]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [h3962, hlam, p3993_1]
            · have p3993_0 := h3993c.1
              have p3993_1 := h3993c.2.1
              have p3993_2 := h3993c.2.2.1
              have p3993_3 := h3993c.2.2.2
              linarith only [hlam, p3993_0]
          · linarith only [h0, h2875, h3898, h3962, h3963, h3992, hc01, hc23, hlam, hphi, ht12]
      · linarith only [h3145, h3898, h3899, h3962, hlam]
    · linarith only [h3145, h3898, h3961, hlam]

end R2N4
