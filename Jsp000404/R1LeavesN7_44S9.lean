import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_44S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5638000 in
set_option maxHeartbeats 5638000 in
theorem r1l7_21_15_M_IR_L_I_s0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_15_M_IR_L_I_s1 m hb1 hb5 h0 h1
  · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

set_option maxHeartbeats 6238000 in
set_option maxHeartbeats 6238000 in
theorem r1l7_21_15_M_IR_L_I (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_M_IR_L_I_s0 m hb1 hb5 h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h2820 | h2820
    · linarith only [h0, h2820, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2822 | h2822
      · linarith only [h0, h2822, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h2824 | h2824
        · linarith only [h0, h2824, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h2826 | h2826
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2827 | h2827
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2828 | h2828
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2829 | h2829
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2830 | h2830
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2831 | h2831
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2832 | h2832
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2833 | h2833
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2834 | h2834
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2835 | h2835
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2836 | h2836
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2837 | h2837
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2838 | h2838
                                  · rcases h1bigk with h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c | h2839c
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h0, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2820, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2822, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2824, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2839_1, u1ehi2]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2839_1, u1ehi3]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2829, hlam, p2839_1]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2830, hlam, p2839_1]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2832, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2839_1, u1ehi0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2831, hlam, p2839_1]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2833, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [h2834, hlam, p2839_0]
                                    · have p2839_0 := h2839c.1
                                      have p2839_1 := h2839c.2.1
                                      have p2839_2 := h2839c.2.2.1
                                      have p2839_3 := h2839c.2.2.2
                                      linarith only [hlam, p2839_0]
                                  · rcases h1bigk with h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c | h2865c
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h0, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2820, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2822, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2824, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2865_1, u1ehi2]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2822, hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2829, hlam, p2865_1]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2830, hlam, p2865_1]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2832, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2865_1, u1ehi0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2831, hlam, p2865_1]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2833, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [h2834, hlam, p2865_0]
                                    · have p2865_0 := h2865c.1
                                      have p2865_1 := h2865c.2.1
                                      have p2865_2 := h2865c.2.2.1
                                      have p2865_3 := h2865c.2.2.2
                                      linarith only [hlam, p2865_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2891 | h2891
                                  · linarith only [h0, h2826, h2835, h2837, h2891, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c | h2893c
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h0, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2820, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2822, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2824, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2893_1, u1ehi2]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2822, hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2829, hlam, p2893_1]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2830, hlam, p2893_1]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2832, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2893_1, u1ehi0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2831, hlam, p2893_1]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2833, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [h2834, hlam, p2893_0]
                                    · have p2893_0 := h2893c.1
                                      have p2893_1 := h2893c.2.1
                                      have p2893_2 := h2893c.2.2.1
                                      have p2893_3 := h2893c.2.2.2
                                      linarith only [hlam, p2893_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2919 | h2919
                                · linarith only [h2835, h2836, h2919, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2921 | h2921
                                  · linarith only [h2835, h2836, h2919, h2921, hlam]
                                  · rcases h1bigk with h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c | h2923c
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h0, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2820, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2822, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2824, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2822, h2828, h2832, h2836, h2921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2822, h2828, h2835, h2836, h2921, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2923_1, u1ehi4]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2829, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2822, h2828, h2829, h2835, h2836, h2921, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2830, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2832, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2923_1, u1ehi0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2831, hlam, p2923_1]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2833, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [h2834, hlam, p2923_0]
                                    · have p2923_0 := h2923c.1
                                      have p2923_1 := h2923c.2.1
                                      have p2923_2 := h2923c.2.2.1
                                      have p2923_3 := h2923c.2.2.2
                                      linarith only [hlam, p2923_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2949 | h2949
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2950 | h2950
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2951 | h2951
                                  · rcases h1bigk with h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h0, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2820, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2822, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2824, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2952_1, u1ehi2]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2952_1, u1ehi3]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2829, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2830, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2832, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2952_1, u1ehi0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2831, hlam, p2952_1]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2833, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [h2834, hlam, p2952_0]
                                    · have p2952_0 := h2952c.1
                                      have p2952_1 := h2952c.2.1
                                      have p2952_2 := h2952c.2.2.1
                                      have p2952_3 := h2952c.2.2.2
                                      linarith only [hlam, p2952_0]
                                  · linarith only [h2822, h2828, h2829, h2832, h2835, h2949, h2951, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h2835, h2949, h2950, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2980 | h2980
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2981 | h2981
                                  · rcases h1bigk with h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c | h2982c
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h0, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2820, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2822, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2824, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hc12, hlam, hphi, p2982_1, u1ehi2]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2822, hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hc13, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2829, hlam, p2982_1]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hc14, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2830, hlam, p2982_1]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2832, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hc15, hlam, hphi, p2982_1, u1ehi0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2831, hlam, p2982_1]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2833, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [h2834, hlam, p2982_0]
                                    · have p2982_0 := h2982c.1
                                      have p2982_1 := h2982c.2.1
                                      have p2982_2 := h2982c.2.2.1
                                      have p2982_3 := h2982c.2.2.2
                                      linarith only [hlam, p2982_0]
                                  · linarith only [h2835, h2980, h2981, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3009 | h3009
                                  · rcases h1bigk with h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c | h3010c
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h0, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2820, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2822, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2824, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hc12, hlam, hphi, p3010_1, u1ehi2]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2822, hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hc13, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2829, hlam, p3010_1]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hc14, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2830, hlam, p3010_1]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2832, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hc15, hlam, hphi, p3010_1, u1ehi0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2831, hlam, p3010_1]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2833, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [h2834, hlam, p3010_0]
                                    · have p3010_0 := h3010c.1
                                      have p3010_1 := h3010c.2.1
                                      have p3010_2 := h3010c.2.2.1
                                      have p3010_3 := h3010c.2.2.2
                                      linarith only [hlam, p3010_0]
                                  · rcases h1bigk with h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h0, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2820, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2822, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2824, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hc12, hlam, hphi, p3036_1, u1ehi2]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2822, hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2824, hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hc13, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2829, hlam, p3036_1]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2822, h2829, hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2824, h2829, hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hc14, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2830, hlam, p3036_1]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2832, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2824, h2829, h2832, hc12, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hc15, hlam, hphi, p3036_1, u1ehi0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2831, hlam, p3036_1]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2833, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [h2834, hlam, p3036_0]
                                    · have p3036_0 := h3036c.1
                                      have p3036_1 := h3036c.2.1
                                      have p3036_2 := h3036c.2.2.1
                                      have p3036_3 := h3036c.2.2.2
                                      linarith only [hlam, p3036_0]
                          · linarith only [h2822, h2828, h2834, hlam]
                        · linarith only [h2820, h2833, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h2820, h2832, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h2820, h2829, h2831, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h2820, h2829, h2830, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2829, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3068 | h3068
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3069 | h3069
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3070 | h3070
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3071 | h3071
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3072 | h3072
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3073 | h3073
                          · linarith only [h2822, h2828, h3068, h3071, h3073, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h2822, h3073, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                        · linarith only [h0, h2826, h2827, h3072, hc12, hlam, hphi, u1ehi2]
                      · linarith only [h2820, h3071, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h3070, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h2820, h3068, h3069, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2826, h3068, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3081 | h3081
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3082 | h3082
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3083 | h3083
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3084 | h3084
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3085 | h3085
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3086 | h3086
                        · linarith only [h2820, h2827, h3082, h3086, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h2820, h3086, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h2820, h3085, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h3084, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h2820, h3082, h3083, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2826, h3082, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3093 | h3093
                · rcases m.htr 1 2 4 (by decide) (by decide) with h3094 | h3094
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h3095 | h3095
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3096 | h3096
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3097 | h3097
                        · linarith only [h2820, h2827, h3093, h3097, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h2820, h3097, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h2820, h3096, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h3095, hc25, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h0, h3094, hc24, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h2826, h3093, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3104 | h3104
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3105 | h3105
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3106 | h3106
                · linarith only [h0, h2826, h3106, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h3106, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3109 | h3109
                · linarith only [h0, h2826, h3109, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h3109, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3112 | h3112
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3113 | h3113
                · linarith only [h0, h2826, h3113, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h3113, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3116 | h3116
                · linarith only [h0, h2826, h3116, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h3116, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
