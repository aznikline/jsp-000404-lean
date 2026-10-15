import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8819 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8820 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8821 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 5 (by decide) (by decide) with h8822 | h8822
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8823 | h8823
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8824 | h8824
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8825 | h8825
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8826 | h8826
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8827 | h8827
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8828 | h8828
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8829 | h8829
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8830 | h8830
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8831 | h8831
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8832 | h8832
                      · rcases h0bigk with h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h0, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h6421, hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h7464, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8188, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h0, h8188, h8823, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8818, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h6421, h7464, h8824, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8819, hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8821, hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8820, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8822, hlam, p8833_0]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [h8823, hlam, p8833_1]
                        · have p8833_0 := h8833c.1
                          have p8833_1 := h8833c.2.1
                          have p8833_2 := h8833c.2.2.1
                          have p8833_3 := h8833c.2.2.2
                          linarith only [hlam, p8833_0]
                      · rcases h0bigk with h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c | h8859c
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h0, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h6421, hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h7464, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8188, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8818, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h6421, h8819, h8824, h8831, h8832, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8819, hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8821, hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8820, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8822, hlam, p8859_0]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [h8823, hlam, p8859_1]
                        · have p8859_0 := h8859c.1
                          have p8859_1 := h8859c.2.1
                          have p8859_2 := h8859c.2.2.1
                          have p8859_3 := h8859c.2.2.2
                          linarith only [hlam, p8859_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8885 | h8885
                      · linarith only [h0, h8818, h8829, h8831, h8885, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c | h8887c
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h0, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h6421, hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h7464, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8188, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8818, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h6421, h7464, h8824, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8819, hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8821, hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8820, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8822, hlam, p8887_0]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [h8823, hlam, p8887_1]
                        · have p8887_0 := h8887c.1
                          have p8887_1 := h8887c.2.1
                          have p8887_2 := h8887c.2.2.1
                          have p8887_3 := h8887c.2.2.2
                          linarith only [hlam, p8887_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8913 | h8913
                    · linarith only [h8829, h8830, h8913, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8915 | h8915
                      · linarith only [h0, h8818, h8829, h8913, h8915, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h0bigk with h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c | h8917c
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h0, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h6421, hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h7464, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8188, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h0, h8823, h8830, h8915, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8818, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h6421, h8823, h8824, h8830, h8915, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8819, hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8821, hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8820, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8822, hlam, p8917_0]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [h8823, hlam, p8917_1]
                        · have p8917_0 := h8917c.1
                          have p8917_1 := h8917c.2.1
                          have p8917_2 := h8917c.2.2.1
                          have p8917_3 := h8917c.2.2.2
                          linarith only [hlam, p8917_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8943 | h8943
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8944 | h8944
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8945 | h8945
                      · rcases h0bigk with h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c | h8946c
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h0, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h6421, hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h7464, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8188, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8818, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h6421, h8819, h8824, h8829, h8943, h8945, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8819, hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8821, hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8820, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8822, hlam, p8946_0]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [h8823, hlam, p8946_1]
                        · have p8946_0 := h8946c.1
                          have p8946_1 := h8946c.2.1
                          have p8946_2 := h8946c.2.2.1
                          have p8946_3 := h8946c.2.2.2
                          linarith only [hlam, p8946_0]
                      · linarith only [h7464, h8823, h8824, h8827, h8829, h8943, h8945, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8829, h8943, h8944, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8974 | h8974
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8975 | h8975
                      · rcases h0bigk with h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c | h8976c
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h0, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h6421, hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h7464, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8188, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8818, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h6421, h8819, h8824, h8974, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8819, hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8821, hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h7464, h8822, h8824, h8827, h8943, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8820, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8822, hlam, p8976_0]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [h8823, hlam, p8976_1]
                        · have p8976_0 := h8976c.1
                          have p8976_1 := h8976c.2.1
                          have p8976_2 := h8976c.2.2.1
                          have p8976_3 := h8976c.2.2.2
                          linarith only [hlam, p8976_0]
                      · linarith only [h8829, h8974, h8975, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9003 | h9003
                      · rcases h0bigk with h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c | h9004c
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h0, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h6421, hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h7464, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8188, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h0, h8821, h8974, h9003, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8818, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h6421, h7464, h8824, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8819, hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8821, hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8820, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8822, hlam, p9004_0]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [h8823, hlam, p9004_1]
                        · have p9004_0 := h9004c.1
                          have p9004_1 := h9004c.2.1
                          have p9004_2 := h9004c.2.2.1
                          have p9004_3 := h9004c.2.2.2
                          linarith only [hlam, p9004_0]
                      · rcases h0bigk with h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h0, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h6421, hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h7464, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8188, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h6421, h8824, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8818, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h6421, h7464, h8824, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h6421, h8188, h8824, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h7464, h8824, h8827, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8819, hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8821, hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h7464, h8188, h8824, h8827, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8188, h8824, h8827, h8828, hc01, hc12, hlam, hphi, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8820, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8822, hlam, p9030_0]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [h8823, hlam, p9030_1]
                        · have p9030_0 := h9030c.1
                          have p9030_1 := h9030c.2.1
                          have p9030_2 := h9030c.2.2.1
                          have p9030_3 := h9030c.2.2.2
                          linarith only [hlam, p9030_0]
              · linarith only [h7464, h8823, h8828, hlam]
            · linarith only [h6421, h8821, h8827, hlam]
          · linarith only [h0, h8820, h8826, hlam]
        · linarith only [h0, h8819, h8825, hlam]
      · linarith only [h0, h8818, h8824, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9061 | h9061
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9062 | h9062
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9063 | h9063
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9064 | h9064
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9065 | h9065
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9066 | h9066
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9067 | h9067
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9068 | h9068
                    · linarith only [h8819, h8823, h9068, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9070 | h9070
                      · linarith only [h8819, h8823, h9066, h9070, hlam]
                      · rcases h0bigk with h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c | h9072c
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, hlam, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h6421, hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h7464, hlam, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8188, hlam, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h6421, hc01, hc13, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8818, hlam, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, h7464, h8818, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h0, h8188, h8818, hc01, hc12, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8823, h9065, hc01, hc14, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8819, hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8821, hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8823, hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8820, hlam, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8822, hlam, p9072_0]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [h8823, h9065, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9072_1]
                        · have p9072_0 := h9072c.1
                          have p9072_1 := h9072c.2.1
                          have p9072_2 := h9072c.2.2.1
                          have p9072_3 := h9072c.2.2.2
                          linarith only [hlam, p9072_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9098 | h9098
                    · linarith only [h8819, h8823, h9098, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9100 | h9100
                      · linarith only [h8822, h8823, h9066, h9067, h9100, hlam]
                      · rcases h0bigk with h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c | h9102c
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h0, hlam, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h6421, hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h7464, hlam, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8188, hlam, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h0, h8822, h9066, h9067, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h6421, h9061, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8818, hlam, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h6421, h7464, h9061, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h6421, h8822, h9061, h9066, h9067, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h7464, h9061, h9064, hc01, hc12, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8819, hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8821, hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8823, hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8823, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8820, hlam, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8822, hlam, p9102_0]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [h8823, hc04, hc45, hlam, hphi, p9102_1]
                        · have p9102_0 := h9102c.1
                          have p9102_1 := h9102c.2.1
                          have p9102_2 := h9102c.2.2.1
                          have p9102_3 := h9102c.2.2.2
                          linarith only [hlam, p9102_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9128 | h9128
                  · linarith only [h8821, h8823, h9061, h9064, h9065, h9066, h9128, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9130 | h9130
                    · linarith only [h0, h8819, h8821, h8823, h9066, h9130, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9132 | h9132
                      · linarith only [h8821, h8823, h9132, hlam]
                      · rcases h0bigk with h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c | h9134c
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, hlam, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h6421, hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h7464, hlam, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8188, hlam, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, h8821, h9066, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h6421, hc01, hc13, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8818, hlam, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, h8818, h8821, h9066, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h0, h8188, h8818, hc01, hc12, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8823, h9065, hc01, hc14, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8819, hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8821, hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8823, hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8188, h9065, hc01, hc14, hlam, hphi, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8820, hlam, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8822, hlam, p9134_0]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [h8823, h9065, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9134_1]
                        · have p9134_0 := h9134c.1
                          have p9134_1 := h9134c.2.1
                          have p9134_2 := h9134c.2.2.1
                          have p9134_3 := h9134c.2.2.2
                          linarith only [hlam, p9134_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9160 | h9160
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9161 | h9161
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9162 | h9162
                    · linarith only [h7464, h9065, h9162, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9164 | h9164
                      · linarith only [h7464, h8819, h9065, h9160, h9164, hlam]
                      · rcases h0bigk with h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c | h9166c
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h0, hlam, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h6421, hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h7464, hlam, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8188, hlam, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h0, h7464, h8823, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h6421, h9061, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8818, hlam, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h6421, h7464, h9061, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h6421, h7464, h8823, h9061, hc01, hc12, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8819, hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8821, hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8823, hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8820, hlam, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8822, hlam, p9166_0]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [h8823, hc04, hc45, hlam, hphi, p9166_1]
                        · have p9166_0 := h9166c.1
                          have p9166_1 := h9166c.2.1
                          have p9166_2 := h9166c.2.2.1
                          have p9166_3 := h9166c.2.2.2
                          linarith only [hlam, p9166_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9192 | h9192
                    · linarith only [h7464, h9065, h9192, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9194 | h9194
                      · linarith only [h7464, h9065, h9194, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h0, hlam, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h6421, hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h7464, hlam, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8188, hlam, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h0, h8822, h9161, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h6421, h9061, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8818, hlam, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h6421, h7464, h9061, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h6421, h8188, h9061, hc01, hc12, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8819, hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8821, hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8823, hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8820, hlam, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8822, hlam, p9196_0]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [h8823, hc04, hc45, hlam, hphi, p9196_1]
                        · have p9196_0 := h9196c.1
                          have p9196_1 := h9196c.2.1
                          have p9196_2 := h9196c.2.2.1
                          have p9196_3 := h9196c.2.2.2
                          linarith only [hlam, p9196_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9222 | h9222
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9223 | h9223
                    · linarith only [h7464, h8821, h9065, h9160, h9222, h9223, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h9160, h9222, h9223, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9226 | h9226
                    · linarith only [h7464, h9065, h9226, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9228 | h9228
                      · linarith only [h7464, h8821, h9065, h9228, hlam]
                      · rcases h0bigk with h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h0, hlam, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h6421, hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h7464, hlam, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8188, hlam, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h0, h6421, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h6421, h9061, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8818, hlam, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h6421, h7464, h9061, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h6421, h8188, h9061, hc01, hc12, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8819, hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8821, hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8823, hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8188, hc01, hc15, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8820, hlam, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8822, hlam, p9230_0]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [h8823, hc04, hc45, hlam, hphi, p9230_1]
                        · have p9230_0 := h9230c.1
                          have p9230_1 := h9230c.2.1
                          have p9230_2 := h9230c.2.2.1
                          have p9230_3 := h9230c.2.2.2
                          linarith only [hlam, p9230_0]
            · linarith only [h6421, h8821, h9064, hlam]
          · linarith only [h0, h8818, h8820, h8822, h9063, hlam]
        · linarith only [h0, h8819, h9062, hlam]
      · linarith only [h0, h8818, h9061, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9260 | h9260
    · linarith only [h8821, h8822, h9260, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9262 | h9262
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9263 | h9263
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9264 | h9264
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9265 | h9265
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9266 | h9266
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9267 | h9267
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9268 | h9268
                  · linarith only [h0, h6421, h8818, h8822, h9268, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9270 | h9270
                    · linarith only [h8819, h9260, h9270, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9272 | h9272
                      · linarith only [h8818, h8822, h9260, h9267, h9272, hlam]
                      · rcases h0bigk with h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c | h9274c
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h0, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h6421, hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h7464, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8188, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h0, h8818, h9267, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h0, h8188, hc01, hc12, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8822, h9265, h9266, h9272, hc01, hc13, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8818, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h7464, h8822, h9265, h9266, h9272, hc01, hc13, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8822, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h7464, h9265, hc01, hc13, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8819, hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8821, hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h9260, hlam, p9274_0]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8188, h9265, h9266, hc01, hc13, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8820, hlam, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h8822, h9265, h9266, h9272, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [h7464, h8822, h9265, h9266, h9272, hc01, hc13, hlam, hphi, p9274_1]
                        · have p9274_0 := h9274c.1
                          have p9274_1 := h9274c.2.1
                          have p9274_2 := h9274c.2.2.1
                          have p9274_3 := h9274c.2.2.2
                          linarith only [hlam, p9274_0]
                · linarith only [h8821, h8822, h9267, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9301 | h9301
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9302 | h9302
                  · linarith only [h8818, h8822, h9302, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9304 | h9304
                    · linarith only [h7464, h9266, h9304, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9306 | h9306
                      · linarith only [h7464, h8818, h8822, h9266, h9301, h9306, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases h0bigk with h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c | h9308c
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h0, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h6421, hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h7464, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8188, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h0, h8818, h9301, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h0, h7464, hc01, hc12, hlam, hphi, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h0, h8818, h8822, h9301, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8822, hc01, hc35, hlam, hphi, ht12, ht23, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8818, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h7464, h8822, hc01, hc35, hlam, hphi, ht12, ht23, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8822, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h7464, hc01, hc14, hlam, hphi, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8819, hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8821, hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h9260, hlam, p9308_0]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8188, h9266, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8820, hlam, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h8188, h9266, hc03, hc45, hlam, hphi, ht34, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [h7464, h8188, h9266, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9308_1]
                        · have p9308_0 := h9308c.1
                          have p9308_1 := h9308c.2.1
                          have p9308_2 := h9308c.2.2.1
                          have p9308_3 := h9308c.2.2.2
                          linarith only [hlam, p9308_0]
                · linarith only [h8821, h8822, h9301, hc23, hc35, hlam, hphi]
            · linarith only [h8821, h8822, h9265, hc13, hc35, hlam, hphi]
          · linarith only [h0, h8820, h9264, hlam]
        · linarith only [h0, h8819, h9263, hlam]
      · linarith only [h0, h8818, h9262, hlam]

end R2N4
