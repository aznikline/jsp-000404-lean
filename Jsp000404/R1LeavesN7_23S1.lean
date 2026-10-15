import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 5 (by decide) (by decide) with h815 | h815
  · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
    · linarith only [h10, h11, h816, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h818 | h818
      · rcases m.htr 1 4 5 (by decide) (by decide) with h819 | h819
        · rcases m.htr 2 3 4 (by decide) (by decide) with h820 | h820
          · linarith only [h816, h820, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
            · linarith only [h0, h10, h11, h5, h822, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h11, h4, h7, h818, h820, h822, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h11, h818, h819, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h826 | h826
        · rcases m.htr 2 3 4 (by decide) (by decide) with h827 | h827
          · linarith only [h0, h10, h11, h5, h827, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
            · linarith only [h0, h10, h11, h4, h7, h818, h827, h829, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h831 | h831
              · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                · rcases h2bigk with h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c | h833c
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    rcases p833_3 (m.d 0 2) (by simp) with h835 | h835
                    · rcases p833_3 (m.d 1 2) (by simp) with h836 | h836
                      · linarith only [h0, h836, hlam]
                      · rcases p833_3 (m.d 2 3) (by simp) with h838 | h838
                        · linarith only [h4, h838, hlam]
                        · rcases p833_3 (m.d 2 4) (by simp) with h840 | h840
                          · linarith only [h5, h840, hlam]
                          · linarith only [h11, h840, hlam]
                    · linarith only [h0, h835, hlam]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h11, h4, h7, h815, h827, h829, hlam, p833_2]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, h11, h815, h829, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h11, h5, h815, hlam, p833_2]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, hlam, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, h11, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h11, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, h11, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h4, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h10, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h827, hlam, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h829, hlam, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h5, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p833_1, u1ehi1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    rcases p833_3 (m.d 0 2) (by simp) with h859 | h859
                    · rcases p833_3 (m.d 1 2) (by simp) with h860 | h860
                      · linarith only [h11, h860, hlam]
                      · linarith only [h10, h860, hlam]
                    · linarith only [h4, h859, hlam]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    rcases p833_3 (m.d 0 2) (by simp) with h865 | h865
                    · rcases p833_3 (m.d 1 2) (by simp) with h866 | h866
                      · linarith only [h11, h866, hlam]
                      · linarith only [h815, h866, hlam]
                    · linarith only [h6, h865, hlam]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h6, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h815, hlam, p833_0]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h0, h815, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [h831, hlam, p833_1]
                  · have p833_0 := h833c.1
                    have p833_1 := h833c.2.1
                    have p833_2 := h833c.2.2.1
                    have p833_3 := h833c.2.2.2
                    linarith only [hlam, p833_0]
                · linarith only [h11, h827, h832, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · linarith only [h11, h815, h818, h826, h831, hc14, hlam, hphi, u1ehi2]
        · linarith only [h11, h815, h826, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h878 | h878
    · linarith only [h10, h11, h878, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h880 | h880
      · linarith only [h10, h815, h880, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h882 | h882
        · rcases m.htr 2 3 4 (by decide) (by decide) with h883 | h883
          · linarith only [h878, h883, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h885 | h885
            · linarith only [h10, h880, h885, hc12, hlam, hphi, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h887 | h887
              · rcases m.htr 3 4 5 (by decide) (by decide) with h888 | h888
                · rcases h2bigk with h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    rcases p889_3 (m.d 0 2) (by simp) with h891 | h891
                    · rcases p889_3 (m.d 1 2) (by simp) with h892 | h892
                      · linarith only [h0, h892, hlam]
                      · rcases p889_3 (m.d 2 3) (by simp) with h894 | h894
                        · linarith only [h4, h894, hlam]
                        · rcases p889_3 (m.d 2 4) (by simp) with h896 | h896
                          · linarith only [h5, h896, hlam]
                          · linarith only [h11, h896, hlam]
                    · linarith only [h0, h891, hlam]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h10, h4, h7, h815, h883, h887, hlam, p889_2]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h0, h10, h815, h887, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h0, h815, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p889_1, u1ehi1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h0, hlam, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h815, h885, hc23, hc35, hlam, hphi, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h11, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h815, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h4, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h10, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h883, hlam, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h885, hlam, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h5, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h0, h10, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p889_1, u1ehi2]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    rcases p889_3 (m.d 0 2) (by simp) with h915 | h915
                    · rcases p889_3 (m.d 1 2) (by simp) with h916 | h916
                      · linarith only [h11, h916, hlam]
                      · linarith only [h10, h916, hlam]
                    · linarith only [h4, h915, hlam]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h0, h10, h4, h7, h815, h883, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p889_1, u1ehi2]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h6, hlam, p889_0]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h10, hc25, hlam, hphi, ht12, p889_1, u1ehi2]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    rcases p889_3 (m.d 0 2) (by simp) with h924 | h924
                    · rcases p889_3 (m.d 1 2) (by simp) with h925 | h925
                      · linarith only [h815, h925, hlam]
                      · linarith only [h10, h925, hlam]
                    · linarith only [h4, h924, hlam]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [h887, hlam, p889_1]
                  · have p889_0 := h889c.1
                    have p889_1 := h889c.2.1
                    have p889_2 := h889c.2.2.1
                    have p889_3 := h889c.2.2.2
                    linarith only [hlam, p889_0]
                · linarith only [h11, h882, h883, h888, hlam]
              · linarith only [h11, h882, h887, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
          · linarith only [h0, h10, h11, h5, h933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h935 | h935
            · linarith only [h0, h10, h11, h4, h7, h882, h9, h935, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h937 | h937
              · linarith only [h0, h10, h11, h4, h7, h882, h933, h937, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
              · linarith only [h10, h11, h937, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10 h11
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10 h11

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
  · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
    · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
      · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
        · rcases m.htr 1 4 5 (by decide) (by decide) with h944 | h944
          · rcases m.htr 2 3 4 (by decide) (by decide) with h945 | h945
            · rcases m.htr 2 3 5 (by decide) (by decide) with h946 | h946
              · rcases m.htr 2 4 5 (by decide) (by decide) with h947 | h947
                · linarith only [h0, h10, h4, h940, h947, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h4, h940, h944, h947, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h10, h940, h944, h946, hc35, hlam, hphi, ht12, ht23, u1ehi4]
            · linarith only [h10, h940, h944, h945, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
            · rcases m.htr 2 3 5 (by decide) (by decide) with h953 | h953
              · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                · linarith only [h0, h10, h4, h940, h954, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                  · linarith only [h944, h956, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · rcases h2bigk with h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      rcases p958_3 (m.d 0 2) (by simp) with h960 | h960
                      · rcases p958_3 (m.d 1 2) (by simp) with h961 | h961
                        · linarith only [h0, h961, hlam]
                        · rcases p958_3 (m.d 2 3) (by simp) with h963 | h963
                          · linarith only [h4, h963, hlam]
                          · linarith only [h10, h963, hlam]
                      · linarith only [h0, h960, hlam]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, h10, h941, h954, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p958_1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h10, h4, h940, hlam, p958_2]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h10, h4, h941, hlam, p958_2]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, hlam, p958_1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h10, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p958_1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, h10, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p958_1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h4, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p958_1, u1ehi1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      rcases p958_3 (m.d 0 2) (by simp) with h978 | h978
                      · rcases p958_3 (m.d 1 2) (by simp) with h979 | h979
                        · linarith only [h10, h979, hlam]
                        · linarith only [h940, h979, hlam]
                      · linarith only [h5, h978, hlam]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      rcases p958_3 (m.d 0 2) (by simp) with h983 | h983
                      · rcases p958_3 (m.d 1 2) (by simp) with h984 | h984
                        · linarith only [h10, h984, hlam]
                        · linarith only [h941, h984, hlam]
                      · linarith only [h6, h983, hlam]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h5, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h940, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h952, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h954, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h6, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h941, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h953, hlam, p958_0]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [h0, h941, h952, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p958_1]
                    · have p958_0 := h958c.1
                      have p958_1 := h958c.2.1
                      have p958_2 := h958c.2.2.1
                      have p958_3 := h958c.2.2.2
                      linarith only [hlam, p958_0]
              · linarith only [h10, h953, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h10, h941, h944, h952, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h10, h941, h943, hlam]
      · linarith only [h10, h940, h942, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1002 | h1002
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
          · linarith only [h1004, h940, h941, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1007 | h1007
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1008 | h1008
                · linarith only [h1004, h1007, h1008, h940, h941, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                  · linarith only [h1006, h1008, h1010, h940, h941, hlam]
                  · rcases h2bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      rcases p1012_3 (m.d 0 2) (by simp) with h1014 | h1014
                      · rcases p1012_3 (m.d 1 2) (by simp) with h1015 | h1015
                        · linarith only [h0, h1015, hlam]
                        · rcases p1012_3 (m.d 2 3) (by simp) with h1017 | h1017
                          · linarith only [h1017, h4, hlam]
                          · linarith only [h10, h1017, hlam]
                      · linarith only [h0, h1014, hlam]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, h1007, h940, h941, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1012_1]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h1007, h4, h940, h941, hlam, p1012_2]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, h941, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1012_1, u1ehi1]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, hlam, p1012_1]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h10, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, h1007, h4, h941, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1012_1]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h941, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h4, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1012_1, u1ehi1]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      rcases p1012_3 (m.d 0 2) (by simp) with h1032 | h1032
                      · rcases p1012_3 (m.d 1 2) (by simp) with h1033 | h1033
                        · linarith only [h10, h1033, hlam]
                        · linarith only [h1033, h940, hlam]
                      · linarith only [h1032, h5, hlam]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h0, h4, h940, h941, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1012_1, u1ehi3]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h5, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h940, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h1006, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h1008, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h6, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h940, hc25, hlam, hphi, ht12, p1012_1, u1ehi3]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [h1007, hlam, p1012_0]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      rcases p1012_3 (m.d 0 2) (by simp) with h1046 | h1046
                      · rcases p1012_3 (m.d 1 2) (by simp) with h1047 | h1047
                        · linarith only [h1047, h941, hlam]
                        · linarith only [h1047, h940, hlam]
                      · linarith only [h1046, h5, hlam]
                    · have p1012_0 := h1012c.1
                      have p1012_1 := h1012c.2.1
                      have p1012_2 := h1012c.2.2.1
                      have p1012_3 := h1012c.2.2.2
                      linarith only [hlam, p1012_0]
              · linarith only [h10, h1003, h1007, h940, hc13, hlam, hphi, u1ehi3]
            · linarith only [h0, h10, h1006, h4, h7, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1054 | h1054
          · linarith only [h10, h1003, h1054, h940, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1056 | h1056
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1057 | h1057
              · linarith only [h10, h1003, h1057, h940, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h0, h10, h1057, h4, h8, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
            · linarith only [h10, h1056, h940, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h10, h1002, h940, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1062 | h1062
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1063 | h1063
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1064 | h1064
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1065 | h1065
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1066 | h1066
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1067 | h1067
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1068 | h1068
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1069 | h1069
                  · rcases h2bigk with h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c | h1070c
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      rcases p1070_3 (m.d 0 2) (by simp) with h1072 | h1072
                      · rcases p1070_3 (m.d 1 2) (by simp) with h1073 | h1073
                        · linarith only [h0, h1073, hlam]
                        · rcases p1070_3 (m.d 2 3) (by simp) with h1075 | h1075
                          · linarith only [h1075, h4, hlam]
                          · linarith only [h10, h1075, hlam]
                      · linarith only [h0, h1072, hlam]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, h1062, h1066, h940, hc01, hc25, hlam, hphi, ht0b, ht5b, p1070_1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, h1062, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1070_1, u1ehi4]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1062, h1066, h4, h940, hlam, p1070_2]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, hlam, p1070_1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h10, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h940, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, h1066, h4, h940, hc01, hc25, hlam, hphi, ht0b, ht5b, p1070_1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h4, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1070_1, u1ehi1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h0, h4, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1070_1, u1ehi1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      rcases p1070_3 (m.d 0 2) (by simp) with h1091 | h1091
                      · rcases p1070_3 (m.d 1 2) (by simp) with h1092 | h1092
                        · linarith only [h10, h1092, hlam]
                        · linarith only [h1062, h1092, hlam]
                      · linarith only [h1091, h6, hlam]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h5, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1062, hc24, hlam, hphi, ht12, p1070_1, u1ehi4]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1066, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      rcases p1070_3 (m.d 0 2) (by simp) with h1100 | h1100
                      · rcases p1070_3 (m.d 1 2) (by simp) with h1101 | h1101
                        · linarith only [h1101, h940, hlam]
                        · linarith only [h1062, h1101, hlam]
                      · linarith only [h1100, h6, hlam]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h6, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1062, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1067, hlam, p1070_0]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [h1068, hlam, p1070_1]
                    · have p1070_0 := h1070c.1
                      have p1070_1 := h1070c.2.1
                      have p1070_2 := h1070c.2.2.1
                      have p1070_3 := h1070c.2.2.2
                      linarith only [hlam, p1070_0]
                  · linarith only [h0, h10, h1062, h1068, h1069, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1068, h940, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · linarith only [h1066, h1067, h940, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h0, h10, h1062, h1066, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
          · linarith only [h1062, h1065, h940, hlam]
        · linarith only [h1062, h1063, h1064, h940, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1116 | h1116
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
            · linarith only [h1063, h1118, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h10, h1062, h1118, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · linarith only [h10, h1062, h1063, h1117, hlam]
        · linarith only [h10, h1062, h1116, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1123 | h1123
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1127 | h1127
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1128 | h1128
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1129 | h1129
                  · rcases h2bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      rcases p1130_3 (m.d 0 2) (by simp) with h1132 | h1132
                      · rcases p1130_3 (m.d 1 2) (by simp) with h1133 | h1133
                        · linarith only [h0, h1133, hlam]
                        · rcases p1130_3 (m.d 2 3) (by simp) with h1135 | h1135
                          · linarith only [h1135, h4, hlam]
                          · linarith only [h10, h1135, hlam]
                      · linarith only [h0, h1132, hlam]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, h1126, h1128, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, h1128, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, hlam, p1130_1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h10, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h940, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h1062, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h4, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hc23, hlam, hphi, ht12, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, h1128, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h5, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hc24, hlam, hphi, ht12, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h1126, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h0, h1062, h1126, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h6, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hc25, hlam, hphi, ht12, p1130_1, u1ehi1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h1127, hlam, p1130_0]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [h1128, hlam, p1130_1]
                    · have p1130_0 := h1130c.1
                      have p1130_1 := h1130c.2.1
                      have p1130_2 := h1130c.2.2.1
                      have p1130_3 := h1130c.2.2.2
                      linarith only [hlam, p1130_0]
                  · rcases h2bigk with h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      rcases p1162_3 (m.d 0 2) (by simp) with h1164 | h1164
                      · rcases p1162_3 (m.d 1 2) (by simp) with h1165 | h1165
                        · linarith only [h0, h1165, hlam]
                        · rcases p1162_3 (m.d 2 3) (by simp) with h1167 | h1167
                          · linarith only [h1167, h4, hlam]
                          · linarith only [h10, h1167, hlam]
                      · linarith only [h0, h1164, hlam]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h10, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h1062, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, hlam, p1162_1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h10, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h940, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h1062, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h4, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hc23, hlam, hphi, ht12, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h4, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi3]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h1062, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h5, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hc24, hlam, hphi, ht12, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h1126, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h0, h1062, h1126, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h6, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hc25, hlam, hphi, ht12, p1162_1, u1ehi1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h1127, hlam, p1162_0]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [h1128, hlam, p1162_1]
                    · have p1162_0 := h1162c.1
                      have p1162_1 := h1162c.2.1
                      have p1162_2 := h1162c.2.2.1
                      have p1162_3 := h1162c.2.2.2
                      linarith only [hlam, p1162_0]
                · linarith only [h1125, h1128, h940, hc14, hlam, hphi, u1ehi1]
              · linarith only [h0, h10, h1127, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h10, h1126, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1197 | h1197
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1198 | h1198
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1199 | h1199
                · linarith only [h1125, h1197, h1199, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h0, h1199, h4, h7, h9, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h10, h1124, h1198, hc13, hlam, hphi, u1ehi1]
            · linarith only [h0, h10, h1197, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1204 | h1204
          · linarith only [h1123, h1124, h1204, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1207 | h1207
              · linarith only [h0, h1123, h1124, h1207, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h10, h1207, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h10, h1206, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1211 | h1211
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1212 | h1212
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1213 | h1213
            · linarith only [h1062, h1123, h1211, h1213, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h0, h10, h1213, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h1123, h1211, h1212, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1217 | h1217
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1218 | h1218
            · linarith only [h1123, h1218, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h0, h10, h1218, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1221 | h1221
            · linarith only [h0, h10, h1123, h1221, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h10, h1221, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9 h10

end R2N4
