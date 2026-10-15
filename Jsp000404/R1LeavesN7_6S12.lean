import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 0 3 5 (by decide) (by decide) with h6800 | h6800
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6801 | h6801
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6802 | h6802
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6803 | h6803
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6804 | h6804
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6805 | h6805
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6806 | h6806
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6807 | h6807
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6808 | h6808
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6809 | h6809
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6810 | h6810
                      · linarith only [h6793, h6802, h6807, h6810, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h6793, h6805, h6806, h6810, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h6793, h6805, h6806, h6809, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h6793, h6800, h6807, h6808, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h6793, h6805, h6807, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6816 | h6816
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6817 | h6817
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6818 | h6818
                    · linarith only [h6803, h6806, h6818, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6820 | h6820
                      · linarith only [h6803, h6806, h6816, h6820, hlam]
                      · rcases h0bigk with h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c | h6822c
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h0, hlam, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h0, h6799, h6801, h6806, hc14, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h0, h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h0, h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6793, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6799, h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6793, hlam, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6796, hlam, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6793, h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h0, h6793, h6801, h6803, h6806, h6816, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6794, hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6797, hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6799, hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6801, h6803, h6806, h6816, hc34, hlam, hphi, ht0b, ht45, ht5b, p6822_1, u0elo3]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6795, hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6798, hlam, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6800, hlam, p6822_0]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [h6801, hlam, p6822_1]
                        · have p6822_0 := h6822c.1
                          have p6822_1 := h6822c.2.1
                          have p6822_2 := h6822c.2.2.1
                          have p6822_3 := h6822c.2.2.2
                          linarith only [hlam, p6822_0]
                  · linarith only [h0, h6793, h6800, h6816, h6817, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h6793, h6805, h6816, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6850 | h6850
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6851 | h6851
                · linarith only [h6802, h6805, h6851, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6853 | h6853
                  · linarith only [h0, h6793, h6799, h6802, h6805, h6853, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6855 | h6855
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6856 | h6856
                      · rcases h0bigk with h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h0, hlam, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h0, h6799, h6805, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h0, h6794, h6803, h6855, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h0, h6800, h6853, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6793, h6802, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6799, h6802, h6805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6799, h6802, h6805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6800, h6853, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6793, hlam, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6796, hlam, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6793, h6799, h6802, h6805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h0, h6793, h6800, h6853, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6794, hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6797, hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6799, hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6800, h6853, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6857_1, u0elo3]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6795, hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6798, hlam, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6800, hlam, p6857_0]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [h6801, hlam, p6857_1]
                        · have p6857_0 := h6857c.1
                          have p6857_1 := h6857c.2.1
                          have p6857_2 := h6857c.2.2.1
                          have p6857_3 := h6857c.2.2.2
                          linarith only [hlam, p6857_0]
                      · linarith only [h0, h6794, h6802, h6803, h6805, h6855, h6856, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6793, h6799, h6805, h6850, h6855, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6885 | h6885
                · linarith only [h6802, h6805, h6885, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6887 | h6887
                  · linarith only [h0, h6793, h6799, h6801, h6802, h6805, h6850, h6887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6889 | h6889
                    · linarith only [h6797, h6805, h6850, h6889, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6891 | h6891
                      · linarith only [h0, h6793, h6799, h6802, h6805, h6850, h6891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h6801, h6802, h6805, h6891, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h6798, h6804, hlam]
        · linarith only [h0, h6797, h6803, hlam]
      · linarith only [h0, h6796, h6802, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6897 | h6897
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6898 | h6898
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6899 | h6899
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6900 | h6900
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6901 | h6901
              · linarith only [h6794, h6801, h6901, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6903 | h6903
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6904 | h6904
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6905 | h6905
                    · linarith only [h6795, h6801, h6898, h6901, h6905, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6907 | h6907
                      · linarith only [h6794, h6801, h6898, h6903, h6907, hlam]
                      · rcases h0bigk with h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c | h6909c
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h0, hlam, p6909_1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h0, h6799, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6909_1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6913 | h6913
                          · rcases p6909_3 (m.d 0 2) (by simp) with h6914 | h6914
                            · rcases p6909_3 (m.d 0 3) (by simp) with h6915 | h6915
                              · linarith only [h6793, h6915, hlam]
                              · linarith only [h6799, h6915, hlam]
                            · linarith only [h6797, h6914, hlam]
                          · linarith only [h6794, h6913, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6920 | h6920
                          · rcases p6909_3 (m.d 0 2) (by simp) with h6921 | h6921
                            · rcases p6909_3 (m.d 0 3) (by simp) with h6922 | h6922
                              · linarith only [h6793, h6922, hlam]
                              · linarith only [h6800, h6922, hlam]
                            · linarith only [h6798, h6921, hlam]
                          · linarith only [h6795, h6920, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6793, h6897, h6904, h6907, hc34, hlam, hphi, ht0b, ht45, ht5b, p6909_1, u0elo1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6793, h6897, h6904, h6907, hc34, hlam, hphi, ht0b, ht45, ht5b, p6909_1, u0elo1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6930 | h6930
                          · linarith only [h0, h6930, hlam]
                          · linarith only [h6794, h6930, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6933 | h6933
                          · linarith only [h0, h6933, hlam]
                          · linarith only [h6795, h6933, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6793, hlam, p6909_1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6796, hlam, p6909_1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6939 | h6939
                          · rcases p6909_3 (m.d 0 2) (by simp) with h6940 | h6940
                            · rcases p6909_3 (m.d 0 3) (by simp) with h6941 | h6941
                              · rcases p6909_3 (m.d 0 4) (by simp) with h6942 | h6942
                                · linarith only [h6799, h6942, hlam]
                                · rcases p6909_3 (m.d 0 5) (by simp) with h6944 | h6944
                                  · linarith only [h6800, h6944, hlam]
                                  · linarith only [h6801, h6944, hlam]
                              · linarith only [h6799, h6941, hlam]
                            · linarith only [h6797, h6940, hlam]
                          · linarith only [h6794, h6939, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h6950 | h6950
                          · rcases p6909_3 (m.d 0 2) (by simp) with h6951 | h6951
                            · rcases p6909_3 (m.d 0 3) (by simp) with h6952 | h6952
                              · rcases p6909_3 (m.d 0 4) (by simp) with h6953 | h6953
                                · linarith only [h6799, h6953, hlam]
                                · rcases p6909_3 (m.d 0 5) (by simp) with h6955 | h6955
                                  · linarith only [h6800, h6955, hlam]
                                  · rcases h0emin with h6957 | h6957 | h6957 | h6957 | h6957
                                    · rcases h2bigk with h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c | h6958c
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h0, hlam, p6958_1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6904, h6907, hc34, hlam, hphi, ht0b, ht45, ht5b, p6958_1, u0elo1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        rcases p6958_3 (m.d 0 2) (by simp) with h6962 | h6962
                                        · rcases p6958_3 (m.d 1 2) (by simp) with h6963 | h6963
                                          · rcases p6958_3 (m.d 2 3) (by simp) with h6964 | h6964
                                            · linarith only [h6796, h6964, hlam]
                                            · linarith only [h6903, h6964, hlam]
                                          · linarith only [h6898, h6963, hlam]
                                        · linarith only [h6962, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        rcases p6958_3 (m.d 0 2) (by simp) with h6969 | h6969
                                        · rcases p6958_3 (m.d 1 2) (by simp) with h6970 | h6970
                                          · rcases p6958_3 (m.d 2 3) (by simp) with h6971 | h6971
                                            · linarith only [h6796, h6971, hlam]
                                            · linarith only [h6904, h6971, hlam]
                                          · linarith only [h6899, h6970, hlam]
                                        · linarith only [h6969, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h0, h6793, h6794, h6801, h6898, h6903, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6909_1, p6958_1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        rcases p6958_3 (m.d 0 2) (by simp) with h6978 | h6978
                                        · linarith only [h0, h6978, hlam]
                                        · linarith only [h6796, h6978, hlam]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h0, h6793, h6794, h6801, h6898, hlam, p6909_1, p6958_2]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h0, h6793, h6798, hlam, p6909_1, p6958_2]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6796, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6897, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6793, h6897, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p6958_1, u0elo0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h0, h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p6958_1, u0elo1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6797, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6898, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6903, hlam, p6958_1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6905, hlam, p6958_1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6798, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6899, hlam, p6958_0]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6904, hlam, p6958_1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p6958_1, u0elo1]
                                      · have p6958_0 := h6958c.1
                                        have p6958_1 := h6958c.2.1
                                        have p6958_2 := h6958c.2.2.1
                                        have p6958_3 := h6958c.2.2.2
                                        linarith only [hlam, p6958_0]
                                    · rcases h2bigk with h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c | h6998c
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h0, hlam, p6998_1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p6998_1, u0elo1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        rcases p6998_3 (m.d 0 2) (by simp) with h7002 | h7002
                                        · rcases p6998_3 (m.d 1 2) (by simp) with h7003 | h7003
                                          · rcases p6998_3 (m.d 2 3) (by simp) with h7004 | h7004
                                            · linarith only [h6796, h7004, hlam]
                                            · linarith only [h6903, h7004, hlam]
                                          · linarith only [h6898, h7003, hlam]
                                        · linarith only [h7002, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        rcases p6998_3 (m.d 0 2) (by simp) with h7009 | h7009
                                        · rcases p6998_3 (m.d 1 2) (by simp) with h7010 | h7010
                                          · rcases p6998_3 (m.d 2 3) (by simp) with h7011 | h7011
                                            · linarith only [h6796, h7011, hlam]
                                            · linarith only [h6904, h7011, hlam]
                                          · linarith only [h6899, h7010, hlam]
                                        · linarith only [h7009, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6957, hc12, hlam, ht01, p6998_1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        rcases p6998_3 (m.d 0 2) (by simp) with h7018 | h7018
                                        · linarith only [h0, h7018, hlam]
                                        · linarith only [h6796, h7018, hlam]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h0, h6793, h6794, h6801, h6898, hlam, p6909_1, p6998_2]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h0, h6793, h6795, h6899, hlam, p6909_1, p6998_2]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6796, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6897, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p6998_1, u0elo1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p6998_1, u0elo0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6797, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6898, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6903, hlam, p6998_1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6905, hlam, p6998_1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6798, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6899, hlam, p6998_0]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6904, hlam, p6998_1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p6998_1, u0elo1]
                                      · have p6998_0 := h6998c.1
                                        have p6998_1 := h6998c.2.1
                                        have p6998_2 := h6998c.2.2.1
                                        have p6998_3 := h6998c.2.2.2
                                        linarith only [hlam, p6998_0]
                                    · rcases h2bigk with h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c | h7038c
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h0, hlam, p7038_1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7038_1, u0elo1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        rcases p7038_3 (m.d 0 2) (by simp) with h7042 | h7042
                                        · rcases p7038_3 (m.d 1 2) (by simp) with h7043 | h7043
                                          · rcases p7038_3 (m.d 2 3) (by simp) with h7044 | h7044
                                            · linarith only [h6796, h7044, hlam]
                                            · linarith only [h6903, h7044, hlam]
                                          · linarith only [h6898, h7043, hlam]
                                        · linarith only [h7042, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        rcases p7038_3 (m.d 0 2) (by simp) with h7049 | h7049
                                        · rcases p7038_3 (m.d 1 2) (by simp) with h7050 | h7050
                                          · rcases p7038_3 (m.d 2 3) (by simp) with h7051 | h7051
                                            · linarith only [h6796, h7051, hlam]
                                            · linarith only [h6904, h7051, hlam]
                                          · linarith only [h6899, h7050, hlam]
                                        · linarith only [h7049, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h0, h6793, h6794, h6801, h6898, h6903, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6909_1, p7038_1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        rcases p7038_3 (m.d 0 2) (by simp) with h7058 | h7058
                                        · linarith only [h0, h7058, hlam]
                                        · linarith only [h6796, h7058, hlam]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h0, h6793, h6794, h6801, h6898, hlam, p6909_1, p7038_2]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h0, h6793, h6795, h6899, hlam, p6909_1, p7038_2]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6796, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6897, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7038_1, u0elo1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p7038_1, u0elo0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6797, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6898, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6903, hlam, p7038_1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6905, hlam, p7038_1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6798, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6899, hlam, p7038_0]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6904, hlam, p7038_1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7038_1, u0elo1]
                                      · have p7038_0 := h7038c.1
                                        have p7038_1 := h7038c.2.1
                                        have p7038_2 := h7038c.2.2.1
                                        have p7038_3 := h7038c.2.2.2
                                        linarith only [hlam, p7038_0]
                                    · linarith only [h0, h6793, h6801, h6957, hc12, hlam, ht01, p6909_1]
                                    · linarith only [h0, h6793, h6957, hc12, hlam, ht01, p6909_1]
                              · linarith only [h6800, h6952, hlam]
                            · linarith only [h6798, h6951, hlam]
                          · linarith only [h6795, h6950, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6794, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6797, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6799, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6801, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6795, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6798, hlam, p6909_1]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [h6800, hlam, p6909_0]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          rcases p6909_3 (m.d 0 1) (by simp) with h7091 | h7091
                          · rcases p6909_3 (m.d 0 2) (by simp) with h7092 | h7092
                            · rcases p6909_3 (m.d 0 3) (by simp) with h7093 | h7093
                              · rcases p6909_3 (m.d 0 4) (by simp) with h7094 | h7094
                                · linarith only [h6801, h7094, hlam]
                                · rcases p6909_3 (m.d 0 5) (by simp) with h7096 | h7096
                                  · rcases h0emin with h7097 | h7097 | h7097 | h7097 | h7097
                                    · rcases h2bigk with h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h0, hlam, p7098_1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1, u0elo1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        rcases p7098_3 (m.d 0 2) (by simp) with h7102 | h7102
                                        · rcases p7098_3 (m.d 1 2) (by simp) with h7103 | h7103
                                          · rcases p7098_3 (m.d 2 3) (by simp) with h7104 | h7104
                                            · linarith only [h6796, h7104, hlam]
                                            · linarith only [h6903, h7104, hlam]
                                          · linarith only [h6898, h7103, hlam]
                                        · linarith only [h7102, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        rcases p7098_3 (m.d 0 2) (by simp) with h7109 | h7109
                                        · rcases p7098_3 (m.d 1 2) (by simp) with h7110 | h7110
                                          · rcases p7098_3 (m.d 2 3) (by simp) with h7111 | h7111
                                            · linarith only [h6796, h7111, hlam]
                                            · linarith only [h6904, h7111, hlam]
                                          · linarith only [h6899, h7110, hlam]
                                        · linarith only [h7109, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h0, h7097, hc12, hlam, ht01, p7098_1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        rcases p7098_3 (m.d 0 2) (by simp) with h7118 | h7118
                                        · linarith only [h0, h7118, hlam]
                                        · linarith only [h6796, h7118, hlam]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, hlam, p6909_1, p7098_2]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        rcases p7098_3 (m.d 0 2) (by simp) with h7122 | h7122
                                        · linarith only [h0, h7122, hlam]
                                        · linarith only [h6798, h7122, hlam]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6796, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6897, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1, u0elo1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p7098_1, u0elo0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6797, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6898, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6903, hlam, p7098_1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6905, hlam, p7098_1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6798, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6899, hlam, p7098_0]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6904, hlam, p7098_1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1, u0elo1]
                                      · have p7098_0 := h7098c.1
                                        have p7098_1 := h7098c.2.1
                                        have p7098_2 := h7098c.2.2.1
                                        have p7098_3 := h7098c.2.2.2
                                        linarith only [hlam, p7098_0]
                                    · rcases h2bigk with h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c | h7140c
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h0, hlam, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7140_1, u0elo1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        rcases p7140_3 (m.d 0 2) (by simp) with h7144 | h7144
                                        · rcases p7140_3 (m.d 1 2) (by simp) with h7145 | h7145
                                          · rcases p7140_3 (m.d 2 3) (by simp) with h7146 | h7146
                                            · linarith only [h6796, h7146, hlam]
                                            · linarith only [h6903, h7146, hlam]
                                          · linarith only [h6898, h7145, hlam]
                                        · linarith only [h7144, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        rcases p7140_3 (m.d 0 2) (by simp) with h7151 | h7151
                                        · rcases p7140_3 (m.d 1 2) (by simp) with h7152 | h7152
                                          · rcases p7140_3 (m.d 2 3) (by simp) with h7153 | h7153
                                            · linarith only [h6796, h7153, hlam]
                                            · linarith only [h6904, h7153, hlam]
                                          · linarith only [h6899, h7152, hlam]
                                        · linarith only [h7151, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h7097, hc12, hlam, ht01, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        rcases p7140_3 (m.d 0 2) (by simp) with h7160 | h7160
                                        · linarith only [h0, h7160, hlam]
                                        · linarith only [h6796, h7160, hlam]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, hlam, p6909_1, p7140_2]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        rcases p7140_3 (m.d 0 2) (by simp) with h7164 | h7164
                                        · linarith only [h0, h7164, hlam]
                                        · linarith only [h6798, h7164, hlam]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6796, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6897, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7140_1, u0elo1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h0, h6793, h6897, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6797, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6898, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6903, hlam, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6905, hlam, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6798, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6899, hlam, p7140_0]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6904, hlam, p7140_1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7140_1, u0elo1]
                                      · have p7140_0 := h7140c.1
                                        have p7140_1 := h7140c.2.1
                                        have p7140_2 := h7140c.2.2.1
                                        have p7140_3 := h7140c.2.2.2
                                        linarith only [hlam, p7140_0]
                                    · rcases h2bigk with h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c | h7182c
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h0, hlam, p7182_1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7182_1, u0elo1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        rcases p7182_3 (m.d 0 2) (by simp) with h7186 | h7186
                                        · rcases p7182_3 (m.d 1 2) (by simp) with h7187 | h7187
                                          · rcases p7182_3 (m.d 2 3) (by simp) with h7188 | h7188
                                            · linarith only [h6796, h7188, hlam]
                                            · linarith only [h6903, h7188, hlam]
                                          · linarith only [h6898, h7187, hlam]
                                        · linarith only [h7186, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        rcases p7182_3 (m.d 0 2) (by simp) with h7193 | h7193
                                        · rcases p7182_3 (m.d 1 2) (by simp) with h7194 | h7194
                                          · rcases p7182_3 (m.d 2 3) (by simp) with h7195 | h7195
                                            · linarith only [h6796, h7195, hlam]
                                            · linarith only [h6904, h7195, hlam]
                                          · linarith only [h6899, h7194, hlam]
                                        · linarith only [h7193, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, h6903, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6909_1, p7182_1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        rcases p7182_3 (m.d 0 2) (by simp) with h7202 | h7202
                                        · linarith only [h0, h7202, hlam]
                                        · linarith only [h6796, h7202, hlam]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, hlam, p6909_1, p7182_2]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        rcases p7182_3 (m.d 0 2) (by simp) with h7206 | h7206
                                        · linarith only [h0, h7206, hlam]
                                        · linarith only [h6798, h7206, hlam]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6796, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6897, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7182_1, u0elo1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p7182_1, u0elo0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6797, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6898, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6903, hlam, p7182_1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6905, hlam, p7182_1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6798, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6899, hlam, p7182_0]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6904, hlam, p7182_1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7182_1, u0elo1]
                                      · have p7182_0 := h7182c.1
                                        have p7182_1 := h7182c.2.1
                                        have p7182_2 := h7182c.2.2.1
                                        have p7182_3 := h7182c.2.2.2
                                        linarith only [hlam, p7182_0]
                                    · linarith only [h0, h6793, h6800, h7097, hc12, hlam, ht01, p6909_1]
                                    · rcases h2bigk with h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c | h7225c
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h0, hlam, p7225_1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7225_1, u0elo1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        rcases p7225_3 (m.d 0 2) (by simp) with h7229 | h7229
                                        · rcases p7225_3 (m.d 1 2) (by simp) with h7230 | h7230
                                          · rcases p7225_3 (m.d 2 3) (by simp) with h7231 | h7231
                                            · linarith only [h6796, h7231, hlam]
                                            · linarith only [h6903, h7231, hlam]
                                          · linarith only [h6898, h7230, hlam]
                                        · linarith only [h7229, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        rcases p7225_3 (m.d 0 2) (by simp) with h7236 | h7236
                                        · rcases p7225_3 (m.d 1 2) (by simp) with h7237 | h7237
                                          · rcases p7225_3 (m.d 2 3) (by simp) with h7238 | h7238
                                            · linarith only [h6796, h7238, hlam]
                                            · linarith only [h6904, h7238, hlam]
                                          · linarith only [h6899, h7237, hlam]
                                        · linarith only [h7236, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, h6903, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6909_1, p7225_1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        rcases p7225_3 (m.d 0 2) (by simp) with h7245 | h7245
                                        · linarith only [h0, h7245, hlam]
                                        · linarith only [h6796, h7245, hlam]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h0, h6793, h6794, h6800, h6898, hlam, p6909_1, p7225_2]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        rcases p7225_3 (m.d 0 2) (by simp) with h7249 | h7249
                                        · linarith only [h0, h7249, hlam]
                                        · linarith only [h6798, h7249, hlam]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6796, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6897, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6796, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7225_1, u0elo1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6793, h6897, hc25, hlam, hphi, ht0b, ht5b, p7225_1, u0elo0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6797, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6898, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6903, hlam, p7225_1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6905, hlam, p7225_1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6798, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6899, hlam, p7225_0]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6904, hlam, p7225_1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [h6798, h6903, hc34, hlam, hphi, ht0b, ht45, ht5b, p7225_1, u0elo1]
                                      · have p7225_0 := h7225c.1
                                        have p7225_1 := h7225c.2.1
                                        have p7225_2 := h7225c.2.2.1
                                        have p7225_3 := h7225c.2.2.2
                                        linarith only [hlam, p7225_0]
                                  · linarith only [h6801, h7096, hlam]
                              · linarith only [h6799, h7093, hlam]
                            · linarith only [h6797, h7092, hlam]
                          · linarith only [h6794, h7091, hlam]
                        · have p6909_0 := h6909c.1
                          have p6909_1 := h6909c.2.1
                          have p6909_2 := h6909c.2.2.1
                          have p6909_3 := h6909c.2.2.2
                          linarith only [hlam, p6909_0]
                  · linarith only [h0, h6793, h6800, h6903, h6904, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h6793, h6900, h6903, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7274 | h7274
              · linarith only [h0, h6794, h6801, h7274, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7276 | h7276
                · linarith only [h6897, h6900, h7276, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h7278 | h7278
                  · linarith only [h0, h6793, h6799, h6897, h6900, h7278, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7280 | h7280
                    · linarith only [h6797, h6801, h7280, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7282 | h7282
                      · linarith only [h6799, h6801, h7282, hlam]
                      · rcases h0bigk with h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c | h7284c
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h0, hlam, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h0, h6800, h6900, h7282, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h0, h6799, h6900, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h0, h6800, h6900, h7282, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6793, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6800, h6900, h7282, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6799, h6900, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6800, h6900, h7282, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6793, hlam, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6796, hlam, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6793, h6799, h6900, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h0, h6793, h6800, h6900, h7282, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6794, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6797, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6799, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6801, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6795, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6798, hlam, p7284_1]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6800, hlam, p7284_0]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [h6799, h6900, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7284_1, u0elo4]
                        · have p7284_0 := h7284c.1
                          have p7284_1 := h7284c.2.1
                          have p7284_2 := h7284c.2.2.1
                          have p7284_3 := h7284c.2.2.2
                          linarith only [hlam, p7284_0]
          · linarith only [h0, h6798, h6899, hlam]
        · linarith only [h0, h6797, h6898, hlam]
      · linarith only [h0, h6796, h6897, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h7313 | h7313
    · linarith only [h6799, h6800, h7313, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7315 | h7315
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7316 | h7316
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7317 | h7317
          · rcases m.htr 1 3 4 (by decide) (by decide) with h7318 | h7318
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7319 | h7319
              · linarith only [h6794, h7313, h7319, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7321 | h7321
                · rcases m.htr 2 3 5 (by decide) (by decide) with h7322 | h7322
                  · linarith only [h6793, h6800, h7315, h7322, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7324 | h7324
                    · linarith only [h6793, h6794, h6800, h7313, h7315, h7316, h7321, h7324, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7326 | h7326
                      · linarith only [h6793, h7313, h7315, h7321, h7326, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c | h7328c
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h0, hlam, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h0, h6799, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          rcases p7328_3 (m.d 0 1) (by simp) with h7332 | h7332
                          · rcases p7328_3 (m.d 0 2) (by simp) with h7333 | h7333
                            · rcases p7328_3 (m.d 0 3) (by simp) with h7334 | h7334
                              · linarith only [h6793, h7334, hlam]
                              · linarith only [h6799, h7334, hlam]
                            · linarith only [h6797, h7333, hlam]
                          · linarith only [h6794, h7332, hlam]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h0, h6793, h6800, h7315, h7321, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6793, h7315, h7321, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6793, h7315, h7321, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          rcases p7328_3 (m.d 0 1) (by simp) with h7343 | h7343
                          · linarith only [h0, h7343, hlam]
                          · linarith only [h6794, h7343, hlam]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6793, h6800, h7315, h7321, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6793, hlam, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6796, hlam, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6794, h6800, h7316, h7321, h7326, hc34, hc45, hlam, hphi, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6800, hlam, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6794, hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6797, hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6799, hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h7313, hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6795, hlam, p7328_0]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6798, hlam, p7328_1]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [h6793, h7315, h7321, hc34, hlam, hphi, ht0b, ht45, ht5b, p7328_1, u0elo4]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          rcases p7328_3 (m.d 0 1) (by simp) with h7360 | h7360
                          · rcases p7328_3 (m.d 0 2) (by simp) with h7361 | h7361
                            · rcases p7328_3 (m.d 0 3) (by simp) with h7362 | h7362
                              · linarith only [h6800, h7362, hlam]
                              · linarith only [h6799, h7362, hlam]
                            · linarith only [h6797, h7361, hlam]
                          · linarith only [h6794, h7360, hlam]
                        · have p7328_0 := h7328c.1
                          have p7328_1 := h7328c.2.1
                          have p7328_2 := h7328c.2.2.1
                          have p7328_3 := h7328c.2.2.2
                          linarith only [hlam, p7328_0]
                · linarith only [h6799, h6800, h7321, hc23, hc35, hlam, hphi]
            · linarith only [h6799, h6800, h7318, hc13, hc35, hlam, hphi]
          · linarith only [h0, h6798, h7317, hlam]
        · linarith only [h0, h6797, h7316, hlam]
      · linarith only [h0, h6796, h7315, hlam]

end R2N4
