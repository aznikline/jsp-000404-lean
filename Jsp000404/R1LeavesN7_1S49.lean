import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S45
import Jsp000404.R1LeavesN7_1S46
import Jsp000404.R1LeavesN7_1S47
import Jsp000404.R1LeavesN7_1S48

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h30701 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h31058 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 3 5 (by decide) (by decide) with h31794 | h31794
  · rcases m.htr 0 4 5 (by decide) (by decide) with h31795 | h31795
    · rcases m.htr 1 2 3 (by decide) (by decide) with h31796 | h31796
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31797 | h31797
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31798 | h31798
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31799 | h31799
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31800 | h31800
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31801 | h31801
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31802 | h31802
                  · linarith only [h31058, h31794, h31796, h31802, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h22350, h31796, h31799, h31802, hc01, hc12, hlam, hphi]
                · linarith only [h18443, h31058, h31794, h31795, h31796, h31799, h31801, hc01, hc12, hlam, hphi]
              · linarith only [h31058, h31799, h31800, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31807 | h31807
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31808 | h31808
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31809 | h31809
                  · linarith only [h15532, h31799, h31809, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31811 | h31811
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31812 | h31812
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31813 | h31813
                        · rcases h0bigk with h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c | h31814c
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h0, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h15532, hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h18443, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h20697, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h30701, h31798, h31807, hc01, hc13, hlam, hphi, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h22350, hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h30132, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h30701, hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h15532, h31799, hc01, hc34, hlam, hphi, ht12, ht23, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h15532, h31799, hc02, hc34, hlam, hphi, ht23, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h31058, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h0, h15532, h30701, h31799, hc01, hc34, hlam, hphi, ht12, ht23, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h30132, h31797, hc01, hc12, hlam, hphi, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h0, h30132, h31797, hc01, hc12, hlam, hphi, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h30132, h31794, h31797, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h0, h30132, h30701, h31797, hc01, hc12, hlam, hphi, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h20697, h31799, h31807, hc01, hc34, hlam, hphi, ht12, ht23, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h0, h30701, h31798, h31799, h31807, hc01, hc34, hlam, hphi, ht12, ht23, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h31794, hlam, p31814_0]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [h31795, hlam, p31814_1]
                          · have p31814_0 := h31814c.1
                            have p31814_1 := h31814c.2.1
                            have p31814_2 := h31814c.2.2.1
                            have p31814_3 := h31814c.2.2.2
                            linarith only [hlam, p31814_0]
                        · linarith only [h15532, h31799, h31813, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h30132, h31795, h31812, hlam]
                    · linarith only [h22350, h31794, h31811, hlam]
                · linarith only [h18443, h30132, h31795, h31797, h31808, hc01, hc12, hlam, hphi]
              · linarith only [h22350, h31794, h31796, h31807, hlam]
          · linarith only [h0, h30132, h31797, h31798, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h31796, h31797, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31847 | h31847
        · linarith only [h0, h30132, h31796, h31847, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31849 | h31849
          · linarith only [h0, h30701, h31796, h31849, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31851 | h31851
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31852 | h31852
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31853 | h31853
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31854 | h31854
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31855 | h31855
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31856 | h31856
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31857 | h31857
                        · rcases h0bigk with h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c | h31858c
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h15532, hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h18443, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h20697, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, h31849, h31854, h31856, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h22350, hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h30132, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h30701, hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, h31796, h31851, hc02, hc23, hlam, hphi, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, h30701, h31058, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, h31058, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, h31794, h31796, h31851, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, h30701, h31058, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31058, h31794, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h0, h31058, h31794, h31796, h31851, hc01, hc23, hlam, hphi, ht12, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31794, hlam, p31858_0]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [h31795, hlam, p31858_1]
                          · have p31858_0 := h31858c.1
                            have p31858_1 := h31858c.2.1
                            have p31858_2 := h31858c.2.2.1
                            have p31858_3 := h31858c.2.2.2
                            linarith only [hlam, p31858_0]
                        · linarith only [h31058, h31795, h31857, hlam]
                      · linarith only [h0, h30132, h31058, h31794, h31795, h31851, h31856, hc01, hc14, hlam, hphi]
                    · linarith only [h31058, h31796, h31851, h31855, hc03, hc35, hlam, hphi]
                  · linarith only [h31796, h31851, h31854, hlam]
                · linarith only [h18443, h31058, h31794, h31795, h31796, h31851, h31853, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h31058, h31794, h31851, h31852, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31890 | h31890
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31891 | h31891
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31892 | h31892
                  · linarith only [h0, h31849, h31851, h31890, h31892, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h31796, h31892, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15532, h18443, h31794, h31795, h31851, h31891, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h15532, h31794, h31890, hlam]
    · linarith only [h31058, h31794, h31795, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h31898 | h31898
    · rcases m.htr 1 2 3 (by decide) (by decide) with h31899 | h31899
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31900 | h31900
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31901 | h31901
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31902 | h31902
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31903 | h31903
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31904 | h31904
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31905 | h31905
                  · linarith only [h15532, h31058, h31899, h31905, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h22350, h31899, h31902, h31905, hc01, hc12, hlam, hphi]
                · linarith only [h18443, h31898, h31904, hlam]
              · linarith only [h0, h22350, h31058, h31902, h31903, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31910 | h31910
              · linarith only [h0, h22350, h31794, h31902, h31910, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31912 | h31912
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31913 | h31913
                  · linarith only [h15532, h31902, h31913, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31915 | h31915
                    · linarith only [h31899, h31910, h31915, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31917 | h31917
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31918 | h31918
                        · rcases h0bigk with h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c | h31919c
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h0, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h15532, hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h18443, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h20697, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h22350, h31899, hc01, hc13, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h22350, hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h30132, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h30701, hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h15532, h31910, h31918, hc01, hc34, hlam, hphi, ht12, ht23, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h22350, h31899, h31910, h31918, hc02, hc34, hlam, hphi, ht23, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h31058, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h31794, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h30132, h31900, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h0, h30132, h31900, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h15532, h30132, h31900, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [hlam, p31919_0]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h0, h22350, h30132, h31794, h31900, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h30701, h31900, h31917, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h0, h30701, h31900, h31917, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h0, h22350, h30701, h31900, h31917, hc01, hc12, hlam, hphi, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [h31898, hlam, p31919_1]
                          · have p31919_0 := h31919c.1
                            have p31919_1 := h31919c.2.1
                            have p31919_2 := h31919c.2.2.1
                            have p31919_3 := h31919c.2.2.2
                            linarith only [hlam, p31919_0]
                        · linarith only [h0, h22350, h30132, h31058, h31898, h31900, h31918, hc01, hc12, hlam, hphi]
                      · linarith only [h30132, h31898, h31917, hlam]
                · linarith only [h30132, h31898, h31900, h31912, hlam]
          · linarith only [h0, h30132, h31900, h31901, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h31899, h31900, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h31950 | h31950
        · linarith only [h0, h30132, h31899, h31950, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h31952 | h31952
          · linarith only [h0, h30701, h31899, h31952, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h31954 | h31954
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31955 | h31955
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31956 | h31956
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31957 | h31957
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31958 | h31958
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31959 | h31959
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31960 | h31960
                        · rcases h0bigk with h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c | h31961c
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h0, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h15532, hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h18443, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h20697, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h0, h31952, h31957, h31959, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h22350, hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h30132, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h30701, hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31058, h31899, h31954, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31058, h31899, h31954, hc02, hc23, hlam, hphi, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31058, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31794, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31058, h31899, h31954, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h0, h31058, h31899, h31954, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h15532, h31058, h31899, h31954, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [hlam, p31961_0]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h20697, h31058, h31899, h31954, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31794, h31899, h31954, h31960, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h0, h31794, h31899, h31954, h31960, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h0, h22350, h31794, h31899, h31954, h31960, hc01, hc23, hlam, hphi, ht12, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [h31898, hlam, p31961_1]
                          · have p31961_0 := h31961c.1
                            have p31961_1 := h31961c.2.1
                            have p31961_2 := h31961c.2.2.1
                            have p31961_3 := h31961c.2.2.2
                            linarith only [hlam, p31961_0]
                        · linarith only [h31058, h31898, h31960, hlam]
                      · linarith only [h0, h30132, h31058, h31898, h31899, h31954, h31959, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h22350, h31058, h31899, h31954, h31958, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h31899, h31954, h31957, hlam]
                · linarith only [h18443, h31058, h31898, h31899, h31954, h31956, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h22350, h31058, h31954, h31955, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h31993 | h31993
              · linarith only [h0, h22350, h31794, h31954, h31993, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h31995 | h31995
                · rcases m.htr 2 3 4 (by decide) (by decide) with h31996 | h31996
                  · linarith only [h15532, h31954, h31996, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h31899, h31996, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h18443, h31898, h31995, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h32000 | h32000
      · rcases m.htr 1 2 4 (by decide) (by decide) with h32001 | h32001
        · rcases m.htr 1 2 5 (by decide) (by decide) with h32002 | h32002
          · rcases m.htr 1 3 4 (by decide) (by decide) with h32003 | h32003
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32004 | h32004
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32005 | h32005
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32006 | h32006
                  · linarith only [h0, h22350, h31058, h32000, h32006, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h22350, h32003, h32006, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32009 | h32009
                  · linarith only [h0, h22350, h31058, h32000, h32009, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h22350, h32000, h32003, h32009, hc01, hc12, hlam, hphi]
              · linarith only [h0, h22350, h31058, h32003, h32004, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32013 | h32013
              · linarith only [h0, h22350, h31794, h32003, h32013, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32015 | h32015
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32016 | h32016
                  · linarith only [h15532, h32003, h32016, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32018 | h32018
                    · linarith only [h32000, h32013, h32018, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h32020 | h32020
                      · linarith only [h0, h22350, h31058, h31898, h32001, h32020, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h30132, h32015, h32020, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32023 | h32023
                  · linarith only [h0, h22350, h31058, h32000, h32013, h32023, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32025 | h32025
                    · linarith only [h0, h22350, h31794, h32000, h32025, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h32027 | h32027
                      · linarith only [h15532, h32003, h32015, h32027, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h32029 | h32029
                        · linarith only [h0, h22350, h32000, h32003, h32015, h32029, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h22350, h32000, h32003, h32029, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h22350, h32000, h32002, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h22350, h32000, h32001, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h32034 | h32034
        · linarith only [h0, h30132, h32000, h32034, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h32036 | h32036
          · linarith only [h0, h30701, h32000, h32036, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h32038 | h32038
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32039 | h32039
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32040 | h32040
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32041 | h32041
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32042 | h32042
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h32043 | h32043
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h32044 | h32044
                        · linarith only [h0, h22350, h31058, h31898, h32038, h32044, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h22350, h31058, h32040, h32044, hc01, hc14, hlam, hphi]
                      · linarith only [h32034, h32040, h32043, hlam]
                    · linarith only [h32000, h32039, h32042, hlam]
                  · linarith only [h0, h22350, h31794, h32000, h32039, h32041, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32050 | h32050
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h32051 | h32051
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h32052 | h32052
                      · linarith only [h18443, h32040, h32052, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h32034, h32052, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h22350, h32039, h32051, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h22350, h31794, h32000, h32039, h32050, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h22350, h31058, h32038, h32039, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h32058 | h32058
              · linarith only [h0, h22350, h31794, h32038, h32058, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h32060 | h32060
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32061 | h32061
                  · linarith only [h15532, h32038, h32061, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h32000, h32061, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32064 | h32064
                  · linarith only [h0, h32000, h32038, h32064, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h32000, h32064, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h30701 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 3 4 (by decide) (by decide) with h31058 | h31058
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132 h30701 h31058
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132 h30701 h31058

set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 2 5 (by decide) (by decide) with h30701 | h30701
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132 h30701
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132 h30701

set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 2 4 (by decide) (by decide) with h30132 | h30132
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350 h30132

set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 2 3 (by decide) (by decide) with h22350 | h22350
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 h22350

end R2N4
