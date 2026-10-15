import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h4686 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 2 4 5 (by decide) (by decide) with h4687 | h4687
  · rcases m.htr 3 4 5 (by decide) (by decide) with h4688 | h4688
    · rcases h2bigk with h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c | h4689c
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h0, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4692 | h4692
        · rcases p4689_3 (m.d 1 2) (by simp) with h4693 | h4693
          · rcases p4689_3 (m.d 2 3) (by simp) with h4694 | h4694
            · linarith only [h4694, hlam, p4689_0]
            · rcases p4689_3 (m.d 2 4) (by simp) with h4696 | h4696
              · linarith only [h3226, h4696, hlam]
              · linarith only [h3237, h4696, hlam]
          · linarith only [h3231, h4693, hlam]
        · linarith only [h4692, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4701 | h4701
        · rcases p4689_3 (m.d 1 2) (by simp) with h4702 | h4702
          · rcases p4689_3 (m.d 2 3) (by simp) with h4703 | h4703
            · linarith only [h3225, h4703, hlam]
            · rcases p4689_3 (m.d 2 4) (by simp) with h4705 | h4705
              · linarith only [h4705, hlam, p4689_0]
              · rcases p4689_3 (m.d 2 5) (by simp) with h4707 | h4707
                · linarith only [h3227, h4707, hlam]
                · rcases h2emax with h4709 | h4709 | h4709 | h4709 | h4709
                  · linarith only [h4709, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4689_1]
                  · linarith only [h4709, hlam, ht12, u1ehi1]
                  · rcases h4bigk with h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c | h4712c
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3221, hlam, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      rcases p4712_3 (m.d 0 4) (by simp) with h4715 | h4715
                      · rcases p4712_3 (m.d 1 4) (by simp) with h4716 | h4716
                        · rcases p4712_3 (m.d 2 4) (by simp) with h4717 | h4717
                          · linarith only [h3226, h4717, hlam]
                          · rcases p4712_3 (m.d 3 4) (by simp) with h4719 | h4719
                            · linarith only [h3228, h4719, hlam]
                            · linarith only [h3237, h4719, hlam]
                        · linarith only [h3232, h4716, hlam]
                      · linarith only [h3226, h4715, hlam]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3225, h3228, h3237, h4686, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      rcases p4712_3 (m.d 0 4) (by simp) with h4725 | h4725
                      · rcases p4712_3 (m.d 1 4) (by simp) with h4726 | h4726
                        · rcases p4712_3 (m.d 2 4) (by simp) with h4727 | h4727
                          · linarith only [h3226, h4727, hlam]
                          · linarith only [h4687, h4727, hlam]
                        · linarith only [h3236, h4726, hlam]
                      · linarith only [h4725, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3221, hc14, hlam, hphi, p4712_1, u1ehi0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      rcases p4712_3 (m.d 0 4) (by simp) with h4734 | h4734
                      · linarith only [h3221, h4734, hlam]
                      · linarith only [h3226, h4734, hlam]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3231, h3234, h3237, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      rcases p4712_3 (m.d 0 4) (by simp) with h4738 | h4738
                      · linarith only [h3221, h4738, hlam]
                      · linarith only [h3230, h4738, hlam]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3226, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3232, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3237, hlam, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3228, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3234, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3225, h3228, hlam, p4689_2, p4712_1]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      rcases p4712_3 (m.d 0 4) (by simp) with h4750 | h4750
                      · rcases p4712_3 (m.d 1 4) (by simp) with h4751 | h4751
                        · rcases p4712_3 (m.d 2 4) (by simp) with h4752 | h4752
                          · linarith only [h3237, h4752, hlam]
                          · linarith only [h4687, h4752, hlam]
                        · linarith only [h3236, h4751, hlam]
                      · linarith only [h3230, h4750, hlam]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3230, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h3236, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h4687, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [h4688, hlam, p4712_0]
                    · have p4712_0 := h4712c.1
                      have p4712_1 := h4712c.2.1
                      have p4712_2 := h4712c.2.2.1
                      have p4712_3 := h4712c.2.2.2
                      linarith only [hlam, p4712_0]
                  · rcases h4bigk with h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c | h4762c
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3221, hlam, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      rcases p4762_3 (m.d 0 4) (by simp) with h4765 | h4765
                      · rcases p4762_3 (m.d 1 4) (by simp) with h4766 | h4766
                        · rcases p4762_3 (m.d 2 4) (by simp) with h4767 | h4767
                          · linarith only [h3226, h4767, hlam]
                          · rcases p4762_3 (m.d 3 4) (by simp) with h4769 | h4769
                            · linarith only [h3228, h4769, hlam]
                            · linarith only [h3237, h4769, hlam]
                        · linarith only [h3232, h4766, hlam]
                      · linarith only [h3226, h4765, hlam]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3225, h3228, h3237, h4686, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      rcases p4762_3 (m.d 0 4) (by simp) with h4775 | h4775
                      · rcases p4762_3 (m.d 1 4) (by simp) with h4776 | h4776
                        · rcases p4762_3 (m.d 2 4) (by simp) with h4777 | h4777
                          · linarith only [h3226, h4777, hlam]
                          · linarith only [h4687, h4777, hlam]
                        · linarith only [h3236, h4776, hlam]
                      · linarith only [h4775, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3221, hc14, hlam, hphi, p4762_1, u1ehi0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      rcases p4762_3 (m.d 0 4) (by simp) with h4784 | h4784
                      · linarith only [h3221, h4784, hlam]
                      · linarith only [h3226, h4784, hlam]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3231, h3234, h3237, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      rcases p4762_3 (m.d 0 4) (by simp) with h4788 | h4788
                      · linarith only [h3221, h4788, hlam]
                      · linarith only [h3230, h4788, hlam]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3226, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3232, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3237, hlam, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3228, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3234, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3225, h3228, hlam, p4689_2, p4762_1]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      rcases p4762_3 (m.d 0 4) (by simp) with h4800 | h4800
                      · rcases p4762_3 (m.d 1 4) (by simp) with h4801 | h4801
                        · rcases p4762_3 (m.d 2 4) (by simp) with h4802 | h4802
                          · linarith only [h3237, h4802, hlam]
                          · linarith only [h4687, h4802, hlam]
                        · linarith only [h3236, h4801, hlam]
                      · linarith only [h3230, h4800, hlam]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3230, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h3236, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h4687, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [h4688, hlam, p4762_0]
                    · have p4762_0 := h4762c.1
                      have p4762_1 := h4762c.2.1
                      have p4762_2 := h4762c.2.2.1
                      have p4762_3 := h4762c.2.2.2
                      linarith only [hlam, p4762_0]
                  · rcases h4bigk with h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c | h4812c
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3221, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 4) (by simp) with h4815 | h4815
                      · rcases p4812_3 (m.d 1 4) (by simp) with h4816 | h4816
                        · rcases p4812_3 (m.d 2 4) (by simp) with h4817 | h4817
                          · linarith only [h3226, h4817, hlam]
                          · rcases p4812_3 (m.d 3 4) (by simp) with h4819 | h4819
                            · linarith only [h3228, h4819, hlam]
                            · linarith only [h3237, h4819, hlam]
                        · linarith only [h3232, h4816, hlam]
                      · linarith only [h3226, h4815, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3225, h3228, h3237, h4686, h4688, hc02, hc45, hlam, hphi, ht0b, ht5b, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 4) (by simp) with h4825 | h4825
                      · rcases p4812_3 (m.d 1 4) (by simp) with h4826 | h4826
                        · rcases p4812_3 (m.d 2 4) (by simp) with h4827 | h4827
                          · linarith only [h3226, h4827, hlam]
                          · linarith only [h4687, h4827, hlam]
                        · linarith only [h3236, h4826, hlam]
                      · linarith only [h4825, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3221, hc14, hlam, hphi, p4812_1, u1ehi0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 4) (by simp) with h4834 | h4834
                      · linarith only [h3221, h4834, hlam]
                      · linarith only [h3226, h4834, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3231, h3234, h3237, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 4) (by simp) with h4838 | h4838
                      · linarith only [h3221, h4838, hlam]
                      · linarith only [h3230, h4838, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3226, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3232, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3237, hlam, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3228, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3234, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3225, h3228, hlam, p4689_2, p4812_1]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      rcases p4812_3 (m.d 0 4) (by simp) with h4850 | h4850
                      · rcases p4812_3 (m.d 1 4) (by simp) with h4851 | h4851
                        · rcases p4812_3 (m.d 2 4) (by simp) with h4852 | h4852
                          · linarith only [h3237, h4852, hlam]
                          · linarith only [h4687, h4852, hlam]
                        · linarith only [h3236, h4851, hlam]
                      · linarith only [h3230, h4850, hlam]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3230, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h3236, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4687, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [h4688, hlam, p4812_0]
                    · have p4812_0 := h4812c.1
                      have p4812_1 := h4812c.2.1
                      have p4812_2 := h4812c.2.2.1
                      have p4812_3 := h4812c.2.2.2
                      linarith only [hlam, p4812_0]
          · linarith only [h3232, h4702, hlam]
        · linarith only [h4701, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4864 | h4864
        · rcases p4689_3 (m.d 1 2) (by simp) with h4865 | h4865
          · rcases p4689_3 (m.d 2 3) (by simp) with h4866 | h4866
            · linarith only [h3225, h4866, hlam]
            · linarith only [h4686, h4866, hlam]
          · linarith only [h3233, h4865, hlam]
        · linarith only [h4864, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3225, h3228, h3237, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4873 | h4873
        · linarith only [h0, h4873, hlam]
        · linarith only [h3225, h4873, hlam]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4876 | h4876
        · linarith only [h0, h4876, hlam]
        · linarith only [h3226, h4876, hlam]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4879 | h4879
        · linarith only [h0, h4879, hlam]
        · linarith only [h3227, h4879, hlam]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3225, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3231, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3237, hlam, p4689_1]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3225, h3228, h3237, hc02, hc25, hlam, hphi, ht0b, ht5b, p4689_1]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3226, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3232, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h0, h3225, h3228, h3237, h4686, h4688, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4689_1]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        rcases p4689_3 (m.d 0 2) (by simp) with h4891 | h4891
        · rcases p4689_3 (m.d 1 2) (by simp) with h4892 | h4892
          · rcases p4689_3 (m.d 2 3) (by simp) with h4893 | h4893
            · linarith only [h3237, h4893, hlam]
            · linarith only [h4686, h4893, hlam]
          · linarith only [h3233, h4892, hlam]
        · linarith only [h3227, h4891, hlam]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3227, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h3233, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h4686, hlam, p4689_0]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [h4687, hlam, p4689_1]
      · have p4689_0 := h4689c.1
        have p4689_1 := h4689c.2.1
        have p4689_2 := h4689c.2.2.1
        have p4689_3 := h4689c.2.2.2
        linarith only [hlam, p4689_0]
    · linarith only [h3230, h3237, h4686, h4688, hc04, hc35, hlam, hphi, ht0b, ht5b]
  · linarith only [h3237, h4686, h4687, hlam]

end R2N4
