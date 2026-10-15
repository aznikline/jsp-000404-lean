import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h27373 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h27730 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 3 5 (by decide) (by decide) with h27731 | h27731
  · rcases m.htr 0 4 5 (by decide) (by decide) with h27732 | h27732
    · rcases m.htr 1 2 3 (by decide) (by decide) with h27733 | h27733
      · rcases m.htr 1 2 4 (by decide) (by decide) with h27734 | h27734
        · rcases m.htr 1 2 5 (by decide) (by decide) with h27735 | h27735
          · rcases m.htr 1 3 4 (by decide) (by decide) with h27736 | h27736
            · rcases m.htr 1 3 5 (by decide) (by decide) with h27737 | h27737
              · rcases m.htr 1 4 5 (by decide) (by decide) with h27738 | h27738
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27739 | h27739
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27740 | h27740
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27741 | h27741
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27742 | h27742
                        · rcases h0bigk with h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c | h27743c
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h0, hlam, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h14396, hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h16915, hlam, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h18815, hlam, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27373, h27733, h27739, h27741, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h20408, hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h26804, hlam, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27373, hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h20408, h27733, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h0, h20408, h27733, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h16915, h20408, h27733, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h18815, h20408, h27733, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h26804, h27733, h27739, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h0, h26804, h27733, h27739, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27730, hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h0, h26804, h27373, h27733, h27739, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27373, h27733, h27739, h27741, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h0, h27373, h27733, h27739, h27741, hc01, hc12, hlam, hphi, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27731, hlam, p27743_0]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [h27732, hlam, p27743_1]
                          · have p27743_0 := h27743c.1
                            have p27743_1 := h27743c.2.1
                            have p27743_2 := h27743c.2.2.1
                            have p27743_3 := h27743c.2.2.2
                            linarith only [hlam, p27743_0]
                        · rcases h0bigk with h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c | h27769c
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h0, hlam, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h14396, hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h16915, hlam, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h18815, hlam, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h20408, h27733, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h20408, hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h26804, hlam, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h27373, hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h20408, h27733, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h0, h20408, h27733, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h16915, h20408, h27733, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h18815, h20408, h27733, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h26804, h27733, h27739, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h0, h26804, h27733, h27739, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h27730, hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h0, h26804, h27373, h27733, h27739, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h27373, h27733, h27739, h27741, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h0, h27373, h27733, h27739, h27741, hc01, hc12, hlam, hphi, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h27731, hlam, p27769_0]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [h27732, hlam, p27769_1]
                          · have p27769_0 := h27769c.1
                            have p27769_1 := h27769c.2.1
                            have p27769_2 := h27769c.2.2.1
                            have p27769_3 := h27769c.2.2.2
                            linarith only [hlam, p27769_0]
                      · linarith only [h26804, h27732, h27741, hlam]
                    · linarith only [h20408, h27731, h27740, hlam]
                  · linarith only [h20408, h27730, h27739, hlam]
                · linarith only [h26804, h27732, h27734, h27738, hlam]
              · linarith only [h14396, h20408, h27731, h27737, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h20408, h27730, h27733, h27736, hlam]
          · linarith only [h0, h20408, h27733, h27735, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h27733, h27734, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h27803 | h27803
        · linarith only [h0, h26804, h27733, h27803, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h27805 | h27805
          · linarith only [h0, h27373, h27733, h27805, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h27807 | h27807
            · rcases m.htr 1 3 5 (by decide) (by decide) with h27808 | h27808
              · rcases m.htr 1 4 5 (by decide) (by decide) with h27809 | h27809
                · rcases m.htr 2 3 4 (by decide) (by decide) with h27810 | h27810
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h27811 | h27811
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27812 | h27812
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27813 | h27813
                        · rcases h0bigk with h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c | h27814c
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h0, hlam, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h14396, hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h16915, hlam, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h18815, hlam, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h0, h27805, h27810, h27812, hc01, hc23, hlam, hphi, ht12, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h20408, hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h26804, hlam, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h27373, hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27825 | h27825
                            · linarith only [h14396, h27825, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27827 | h27827
                              · linarith only [h20408, h27827, hlam]
                              · linarith only [h0, h27827, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27830 | h27830
                            · linarith only [h14396, h27830, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27832 | h27832
                              · linarith only [h20408, h27832, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27834 | h27834
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27835 | h27835
                                  · linarith only [h27730, h27835, hlam]
                                  · linarith only [h26804, h27835, hlam]
                                · linarith only [h20408, h27834, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27840 | h27840
                            · linarith only [h14396, h27840, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27842 | h27842
                              · linarith only [h20408, h27842, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27844 | h27844
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27845 | h27845
                                  · linarith only [h27730, h27845, hlam]
                                  · rcases p27814_3 (m.d 0 5) (by simp) with h27847 | h27847
                                    · linarith only [h27731, h27847, hlam]
                                    · rcases h2bigk with h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c | h27849c
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, hlam, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h20408, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h26804, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27373, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, h27805, h27810, h27812, hc01, hc23, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27733, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27803, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27805, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        rcases p27849_3 (m.d 0 2) (by simp) with h27860 | h27860
                                        · linarith only [h27860, hlam, p27849_0]
                                        · rcases p27849_3 (m.d 1 2) (by simp) with h27862 | h27862
                                          · linarith only [h27733, h27862, hlam]
                                          · linarith only [h0, h27862, hlam]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, h26804, hc01, hc23, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, h27805, hc01, hc23, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        rcases p27849_3 (m.d 0 2) (by simp) with h27869 | h27869
                                        · linarith only [h27869, hlam, p27849_0]
                                        · rcases p27849_3 (m.d 1 2) (by simp) with h27871 | h27871
                                          · linarith only [h27803, h27871, hlam]
                                          · linarith only [h0, h27871, hlam]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27810, hlam, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, h27805, h27810, hc01, hc23, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        rcases p27849_3 (m.d 0 2) (by simp) with h27878 | h27878
                                        · linarith only [h27878, hlam, p27849_0]
                                        · rcases p27849_3 (m.d 1 2) (by simp) with h27880 | h27880
                                          · linarith only [h27805, h27880, hlam]
                                          · linarith only [h0, h27880, hlam]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27811, hlam, p27849_1]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [h27812, hlam, p27849_0]
                                      · have p27849_0 := h27849c.1
                                        have p27849_1 := h27849c.2.1
                                        have p27849_2 := h27849c.2.2.1
                                        have p27849_3 := h27849c.2.2.2
                                        linarith only [hlam, p27849_0]
                                · linarith only [h27730, h27844, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27888 | h27888
                            · linarith only [h14396, h27888, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27890 | h27890
                              · linarith only [h20408, h27890, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27892 | h27892
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27893 | h27893
                                  · linarith only [h27730, h27893, hlam]
                                  · linarith only [h27732, h27893, hlam]
                                · linarith only [h27731, h27892, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27897 | h27897
                            · linarith only [h16915, h27897, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27899 | h27899
                              · linarith only [h26804, h27899, hlam]
                              · linarith only [h0, h27899, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27902 | h27902
                            · linarith only [h16915, h27902, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27904 | h27904
                              · linarith only [h26804, h27904, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27906 | h27906
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27907 | h27907
                                  · rcases p27814_3 (m.d 0 5) (by simp) with h27908 | h27908
                                    · linarith only [h27732, h27908, hlam]
                                    · linarith only [h27373, h27908, hlam]
                                  · linarith only [h26804, h27907, hlam]
                                · linarith only [h20408, h27906, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h27730, hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27915 | h27915
                            · linarith only [h16915, h27915, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27917 | h27917
                              · linarith only [h26804, h27917, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27919 | h27919
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27920 | h27920
                                  · rcases p27814_3 (m.d 0 5) (by simp) with h27921 | h27921
                                    · linarith only [h27732, h27921, hlam]
                                    · rcases h2bigk with h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c | h27923c
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, hlam, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h20408, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h26804, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27373, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, h27733, hc01, hc23, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27733, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27803, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27805, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        rcases p27923_3 (m.d 0 2) (by simp) with h27934 | h27934
                                        · linarith only [h27934, hlam, p27923_0]
                                        · rcases p27923_3 (m.d 1 2) (by simp) with h27936 | h27936
                                          · linarith only [h27733, h27936, hlam]
                                          · linarith only [h0, h27936, hlam]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, h26804, hc01, hc23, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, h27373, hc01, hc23, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        rcases p27923_3 (m.d 0 2) (by simp) with h27943 | h27943
                                        · linarith only [h27943, hlam, p27923_0]
                                        · rcases p27923_3 (m.d 1 2) (by simp) with h27945 | h27945
                                          · linarith only [h27803, h27945, hlam]
                                          · linarith only [h0, h27945, hlam]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27810, hlam, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, h27805, h27810, hc01, hc23, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        rcases p27923_3 (m.d 0 2) (by simp) with h27952 | h27952
                                        · linarith only [h27952, hlam, p27923_0]
                                        · rcases p27923_3 (m.d 1 2) (by simp) with h27954 | h27954
                                          · linarith only [h27805, h27954, hlam]
                                          · linarith only [h0, h27954, hlam]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27811, hlam, p27923_1]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [h27812, hlam, p27923_0]
                                      · have p27923_0 := h27923c.1
                                        have p27923_1 := h27923c.2.1
                                        have p27923_2 := h27923c.2.2.1
                                        have p27923_3 := h27923c.2.2.2
                                        linarith only [hlam, p27923_0]
                                  · linarith only [h27732, h27920, hlam]
                                · linarith only [h27731, h27919, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27963 | h27963
                            · linarith only [h18815, h27963, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27965 | h27965
                              · linarith only [h27373, h27965, hlam]
                              · linarith only [h0, h27965, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            rcases p27814_3 (m.d 0 1) (by simp) with h27968 | h27968
                            · linarith only [h18815, h27968, hlam]
                            · rcases p27814_3 (m.d 0 2) (by simp) with h27970 | h27970
                              · linarith only [h27373, h27970, hlam]
                              · rcases p27814_3 (m.d 0 3) (by simp) with h27972 | h27972
                                · rcases p27814_3 (m.d 0 4) (by simp) with h27973 | h27973
                                  · rcases p27814_3 (m.d 0 5) (by simp) with h27974 | h27974
                                    · rcases h2bigk with h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c | h27975c
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, hlam, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h20408, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h26804, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27373, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, h27733, hc01, hc23, hlam, hphi, ht12, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27733, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27803, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27805, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        rcases p27975_3 (m.d 0 2) (by simp) with h27986 | h27986
                                        · linarith only [h27986, hlam, p27975_0]
                                        · rcases p27975_3 (m.d 1 2) (by simp) with h27988 | h27988
                                          · linarith only [h27733, h27988, hlam]
                                          · linarith only [h0, h27988, hlam]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h16915, h27803, hc01, hc23, hlam, hphi, ht12, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, h18815, h27805, hc01, hc23, hlam, hphi, ht12, p27814_1, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        rcases p27975_3 (m.d 0 2) (by simp) with h27995 | h27995
                                        · linarith only [h27995, hlam, p27975_0]
                                        · rcases p27975_3 (m.d 1 2) (by simp) with h27997 | h27997
                                          · linarith only [h27803, h27997, hlam]
                                          · linarith only [h0, h27997, hlam]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27810, hlam, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, h18815, h27805, h27810, hc01, hc23, hlam, hphi, ht12, p27814_1, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        rcases p27975_3 (m.d 0 2) (by simp) with h28004 | h28004
                                        · linarith only [h28004, hlam, p27975_0]
                                        · rcases p27975_3 (m.d 1 2) (by simp) with h28006 | h28006
                                          · linarith only [h27805, h28006, hlam]
                                          · linarith only [h0, h28006, hlam]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27811, hlam, p27975_1]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [h27812, hlam, p27975_0]
                                      · have p27975_0 := h27975c.1
                                        have p27975_1 := h27975c.2.1
                                        have p27975_2 := h27975c.2.2.1
                                        have p27975_3 := h27975c.2.2.2
                                        linarith only [hlam, p27975_0]
                                    · linarith only [h27373, h27974, hlam]
                                  · linarith only [h26804, h27973, hlam]
                                · linarith only [h20408, h27972, hlam]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h27731, hlam, p27814_0]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [h27732, hlam, p27814_1]
                          · have p27814_0 := h27814c.1
                            have p27814_1 := h27814c.2.1
                            have p27814_2 := h27814c.2.2.1
                            have p27814_3 := h27814c.2.2.2
                            linarith only [hlam, p27814_0]
                        · rcases h0bigk with h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c | h28019c
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h0, hlam, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h14396, hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h16915, hlam, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h18815, hlam, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h20408, hc01, hc23, hlam, hphi, ht12, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h20408, hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h26804, hlam, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h27373, hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28030 | h28030
                            · linarith only [h14396, h28030, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28032 | h28032
                              · linarith only [h20408, h28032, hlam]
                              · linarith only [h0, h28032, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28035 | h28035
                            · linarith only [h14396, h28035, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28037 | h28037
                              · linarith only [h20408, h28037, hlam]
                              · rcases p28019_3 (m.d 0 3) (by simp) with h28039 | h28039
                                · rcases p28019_3 (m.d 0 4) (by simp) with h28040 | h28040
                                  · linarith only [h27730, h28040, hlam]
                                  · linarith only [h26804, h28040, hlam]
                                · linarith only [h20408, h28039, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h14396, h27732, h27733, h27813, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28046 | h28046
                            · linarith only [h14396, h28046, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28048 | h28048
                              · linarith only [h20408, h28048, hlam]
                              · rcases p28019_3 (m.d 0 3) (by simp) with h28050 | h28050
                                · rcases p28019_3 (m.d 0 4) (by simp) with h28051 | h28051
                                  · linarith only [h27730, h28051, hlam]
                                  · linarith only [h27732, h28051, hlam]
                                · linarith only [h27731, h28050, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28055 | h28055
                            · linarith only [h16915, h28055, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28057 | h28057
                              · linarith only [h26804, h28057, hlam]
                              · linarith only [h0, h28057, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28060 | h28060
                            · linarith only [h16915, h28060, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28062 | h28062
                              · linarith only [h26804, h28062, hlam]
                              · rcases p28019_3 (m.d 0 3) (by simp) with h28064 | h28064
                                · rcases p28019_3 (m.d 0 4) (by simp) with h28065 | h28065
                                  · rcases p28019_3 (m.d 0 5) (by simp) with h28066 | h28066
                                    · linarith only [h27732, h28066, hlam]
                                    · linarith only [h27373, h28066, hlam]
                                  · linarith only [h26804, h28065, hlam]
                                · linarith only [h20408, h28064, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h27730, hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28073 | h28073
                            · linarith only [h16915, h28073, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28075 | h28075
                              · linarith only [h26804, h28075, hlam]
                              · rcases p28019_3 (m.d 0 3) (by simp) with h28077 | h28077
                                · rcases p28019_3 (m.d 0 4) (by simp) with h28078 | h28078
                                  · rcases p28019_3 (m.d 0 5) (by simp) with h28079 | h28079
                                    · linarith only [h27732, h28079, hlam]
                                    · rcases h2bigk with h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c | h28081c
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, hlam, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h20408, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h26804, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27373, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, h27733, hc01, hc23, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27733, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27803, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27805, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        rcases p28081_3 (m.d 0 2) (by simp) with h28092 | h28092
                                        · linarith only [h28092, hlam, p28081_0]
                                        · rcases p28081_3 (m.d 1 2) (by simp) with h28094 | h28094
                                          · linarith only [h27733, h28094, hlam]
                                          · linarith only [h0, h28094, hlam]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h16915, h27803, hc01, hc23, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, h27373, hc01, hc23, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        rcases p28081_3 (m.d 0 2) (by simp) with h28101 | h28101
                                        · linarith only [h28101, hlam, p28081_0]
                                        · rcases p28081_3 (m.d 1 2) (by simp) with h28103 | h28103
                                          · linarith only [h27803, h28103, hlam]
                                          · linarith only [h0, h28103, hlam]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27810, hlam, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, h27805, h27810, hc01, hc23, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        rcases p28081_3 (m.d 0 2) (by simp) with h28110 | h28110
                                        · linarith only [h28110, hlam, p28081_0]
                                        · rcases p28081_3 (m.d 1 2) (by simp) with h28112 | h28112
                                          · linarith only [h27805, h28112, hlam]
                                          · linarith only [h0, h28112, hlam]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27811, hlam, p28081_1]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [h27812, hlam, p28081_0]
                                      · have p28081_0 := h28081c.1
                                        have p28081_1 := h28081c.2.1
                                        have p28081_2 := h28081c.2.2.1
                                        have p28081_3 := h28081c.2.2.2
                                        linarith only [hlam, p28081_0]
                                  · linarith only [h27732, h28078, hlam]
                                · linarith only [h27731, h28077, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28121 | h28121
                            · linarith only [h18815, h28121, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28123 | h28123
                              · linarith only [h27373, h28123, hlam]
                              · linarith only [h0, h28123, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            rcases p28019_3 (m.d 0 1) (by simp) with h28126 | h28126
                            · linarith only [h18815, h28126, hlam]
                            · rcases p28019_3 (m.d 0 2) (by simp) with h28128 | h28128
                              · linarith only [h27373, h28128, hlam]
                              · rcases p28019_3 (m.d 0 3) (by simp) with h28130 | h28130
                                · rcases p28019_3 (m.d 0 4) (by simp) with h28131 | h28131
                                  · rcases p28019_3 (m.d 0 5) (by simp) with h28132 | h28132
                                    · rcases h2bigk with h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c | h28133c
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, hlam, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h20408, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h26804, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27373, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, h27733, hc01, hc23, hlam, hphi, ht12, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27733, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27803, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27805, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        rcases p28133_3 (m.d 0 2) (by simp) with h28144 | h28144
                                        · linarith only [h28144, hlam, p28133_0]
                                        · rcases p28133_3 (m.d 1 2) (by simp) with h28146 | h28146
                                          · linarith only [h27733, h28146, hlam]
                                          · linarith only [h0, h28146, hlam]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h16915, h27803, hc01, hc23, hlam, hphi, ht12, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, h18815, h27805, hc01, hc23, hlam, hphi, ht12, p28019_1, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        rcases p28133_3 (m.d 0 2) (by simp) with h28153 | h28153
                                        · linarith only [h28153, hlam, p28133_0]
                                        · rcases p28133_3 (m.d 1 2) (by simp) with h28155 | h28155
                                          · linarith only [h27803, h28155, hlam]
                                          · linarith only [h0, h28155, hlam]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27810, hlam, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, h18815, h27805, h27810, hc01, hc23, hlam, hphi, ht12, p28019_1, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        rcases p28133_3 (m.d 0 2) (by simp) with h28162 | h28162
                                        · linarith only [h28162, hlam, p28133_0]
                                        · rcases p28133_3 (m.d 1 2) (by simp) with h28164 | h28164
                                          · linarith only [h27805, h28164, hlam]
                                          · linarith only [h0, h28164, hlam]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27811, hlam, p28133_1]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [h27812, hlam, p28133_0]
                                      · have p28133_0 := h28133c.1
                                        have p28133_1 := h28133c.2.1
                                        have p28133_2 := h28133c.2.2.1
                                        have p28133_3 := h28133c.2.2.2
                                        linarith only [hlam, p28133_0]
                                    · linarith only [h27373, h28132, hlam]
                                  · linarith only [h26804, h28131, hlam]
                                · linarith only [h20408, h28130, hlam]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h27731, hlam, p28019_0]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [h27732, hlam, p28019_1]
                          · have p28019_0 := h28019c.1
                            have p28019_1 := h28019c.2.1
                            have p28019_2 := h28019c.2.2.1
                            have p28019_3 := h28019c.2.2.2
                            linarith only [hlam, p28019_0]
                      · linarith only [h26804, h27732, h27812, hlam]
                    · linarith only [h14396, h27731, h27733, h27811, hlam]
                  · linarith only [h0, h27733, h27810, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16915, h27732, h27809, hlam]
              · linarith only [h14396, h27731, h27808, hlam]
            · linarith only [h14396, h27730, h27807, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h28183 | h28183
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28184 | h28184
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28185 | h28185
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28186 | h28186
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28187 | h28187
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28188 | h28188
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28189 | h28189
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28190 | h28190
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28191 | h28191
                      · linarith only [h0, h26804, h27732, h28184, h28191, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h26804, h28186, h28188, h28191, hc01, hc13, hlam, hphi]
                    · linarith only [h20408, h27731, h28190, hlam]
                  · linarith only [h20408, h27730, h28189, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28196 | h28196
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28197 | h28197
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28198 | h28198
                      · linarith only [h28184, h28188, h28198, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28200 | h28200
                        · linarith only [h16915, h20408, h27730, h28188, h28200, hc01, hc23, hlam, hphi, ht12]
                        · rcases h0bigk with h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c | h28202c
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h0, hlam, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h14396, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h16915, hlam, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h18815, hlam, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h26804, h28184, hc01, hc14, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h20408, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h26804, hlam, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h27373, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h20408, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h0, h20408, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h16915, h20408, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h18815, h20408, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h16915, h28188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h0, h26804, h28184, h28188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h27730, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h27732, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h20408, h27731, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h0, h20408, h27731, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h27731, hlam, p28202_0]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [h16915, h20408, h27731, h28183, hc01, hc12, hlam, hphi, p28202_1]
                          · have p28202_0 := h28202c.1
                            have p28202_1 := h28202c.2.1
                            have p28202_2 := h28202c.2.2.1
                            have p28202_3 := h28202c.2.2.2
                            linarith only [hlam, p28202_0]
                    · linarith only [h20408, h27731, h28197, hlam]
                  · linarith only [h0, h16915, h20408, h27730, h28188, h28196, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h14396, h20408, h27731, h28187, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h20408, h27730, h28183, h28186, hlam]
          · linarith only [h0, h20408, h28183, h28185, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h28183, h28184, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28234 | h28234
        · linarith only [h0, h26804, h28183, h28234, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28236 | h28236
          · linarith only [h0, h27373, h28183, h28236, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28238 | h28238
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28239 | h28239
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28240 | h28240
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28241 | h28241
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28242 | h28242
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28243 | h28243
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28244 | h28244
                        · linarith only [h27730, h27732, h28244, hlam]
                        · rcases h0bigk with h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c | h28246c
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h0, hlam, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h14396, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h16915, hlam, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h18815, hlam, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h0, h28236, h28241, h28243, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h20408, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h26804, hlam, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27373, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            rcases p28246_3 (m.d 0 1) (by simp) with h28257 | h28257
                            · linarith only [h14396, h28257, hlam]
                            · rcases p28246_3 (m.d 0 2) (by simp) with h28259 | h28259
                              · linarith only [h20408, h28259, hlam]
                              · linarith only [h0, h28259, hlam]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            rcases p28246_3 (m.d 0 1) (by simp) with h28262 | h28262
                            · linarith only [h14396, h28262, hlam]
                            · rcases p28246_3 (m.d 0 2) (by simp) with h28264 | h28264
                              · linarith only [h20408, h28264, hlam]
                              · rcases p28246_3 (m.d 0 3) (by simp) with h28266 | h28266
                                · rcases p28246_3 (m.d 0 4) (by simp) with h28267 | h28267
                                  · linarith only [h27730, h28267, hlam]
                                  · linarith only [h26804, h28267, hlam]
                                · linarith only [h20408, h28266, hlam]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            rcases p28246_3 (m.d 0 1) (by simp) with h28272 | h28272
                            · linarith only [h14396, h28272, hlam]
                            · rcases p28246_3 (m.d 0 2) (by simp) with h28274 | h28274
                              · linarith only [h20408, h28274, hlam]
                              · rcases p28246_3 (m.d 0 3) (by simp) with h28276 | h28276
                                · rcases p28246_3 (m.d 0 4) (by simp) with h28277 | h28277
                                  · linarith only [h27730, h28277, hlam]
                                  · rcases p28246_3 (m.d 0 5) (by simp) with h28279 | h28279
                                    · linarith only [h27731, h28279, hlam]
                                    · linarith only [h27732, h28279, hlam]
                                · linarith only [h27730, h28276, hlam]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            rcases p28246_3 (m.d 0 1) (by simp) with h28283 | h28283
                            · linarith only [h14396, h28283, hlam]
                            · rcases p28246_3 (m.d 0 2) (by simp) with h28285 | h28285
                              · linarith only [h20408, h28285, hlam]
                              · rcases p28246_3 (m.d 0 3) (by simp) with h28287 | h28287
                                · rcases p28246_3 (m.d 0 4) (by simp) with h28288 | h28288
                                  · linarith only [h27730, h28288, hlam]
                                  · rcases p28246_3 (m.d 0 5) (by simp) with h28290 | h28290
                                    · linarith only [h27731, h28290, hlam]
                                    · rcases h2bigk with h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c | h28292c
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, hlam, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h20408, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h26804, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h27373, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28236, h28241, h28243, hc02, hc23, hlam, hphi, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28183, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28234, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28236, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        rcases p28292_3 (m.d 0 2) (by simp) with h28303 | h28303
                                        · linarith only [h28303, hlam, p28292_0]
                                        · rcases p28292_3 (m.d 1 2) (by simp) with h28305 | h28305
                                          · linarith only [h28183, h28305, hlam]
                                          · linarith only [h0, h28305, hlam]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, h26804, hc01, hc23, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, h28236, hc01, hc23, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        rcases p28292_3 (m.d 0 2) (by simp) with h28312 | h28312
                                        · linarith only [h28312, hlam, p28292_0]
                                        · rcases p28292_3 (m.d 1 2) (by simp) with h28314 | h28314
                                          · linarith only [h28234, h28314, hlam]
                                          · linarith only [h0, h28314, hlam]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28241, hlam, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, h28236, h28241, hc01, hc23, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        rcases p28292_3 (m.d 0 2) (by simp) with h28321 | h28321
                                        · linarith only [h28321, hlam, p28292_0]
                                        · rcases p28292_3 (m.d 1 2) (by simp) with h28323 | h28323
                                          · linarith only [h28236, h28323, hlam]
                                          · linarith only [h0, h28323, hlam]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28242, hlam, p28292_1]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [h28243, hlam, p28292_0]
                                      · have p28292_0 := h28292c.1
                                        have p28292_1 := h28292c.2.1
                                        have p28292_2 := h28292c.2.2.1
                                        have p28292_3 := h28292c.2.2.2
                                        linarith only [hlam, p28292_0]
                                · linarith only [h27731, h28287, hlam]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27732, h28183, h28238, h28240, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h0, h27732, h28183, h28238, h28240, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27730, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27732, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27732, h28183, h28238, h28240, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h0, h27732, h28183, h28238, h28240, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h27731, hlam, p28246_0]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [h16915, h27732, h28183, h28238, h28240, hc01, hc23, hlam, hphi, ht12, p28246_1]
                          · have p28246_0 := h28246c.1
                            have p28246_1 := h28246c.2.1
                            have p28246_2 := h28246c.2.2.1
                            have p28246_3 := h28246c.2.2.2
                            linarith only [hlam, p28246_0]
                      · linarith only [h0, h26804, h28183, h28238, h28240, h28243, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h27731, h27732, h28183, h28238, h28240, h28242, hlam]
                  · linarith only [h16915, h27730, h28183, h28238, h28241, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28344 | h28344
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28345 | h28345
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28346 | h28346
                      · linarith only [h16915, h28240, h28344, h28346, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h28234, h28346, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h14396, h20408, h27731, h28345, hc01, hc13, hlam, hphi]
                  · linarith only [h14396, h27730, h28183, h28344, hlam]
              · linarith only [h14396, h27731, h28239, hlam]
            · linarith only [h14396, h27730, h28238, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h28353 | h28353
    · linarith only [h27730, h27731, h28353, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h28355 | h28355
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28356 | h28356
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28357 | h28357
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28358 | h28358
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28359 | h28359
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28360 | h28360
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28361 | h28361
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28362 | h28362
                    · linarith only [h27730, h27731, h28355, h28362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h20408, h28355, h28359, h28362, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14396, h20408, h27730, h28355, h28361, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28366 | h28366
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28367 | h28367
                    · linarith only [h27730, h27731, h28355, h28367, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h20408, h28355, h28359, h28367, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14396, h20408, h27730, h28355, h28366, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28371 | h28371
                · linarith only [h16915, h28353, h28358, h28359, h28371, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28373 | h28373
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28374 | h28374
                    · linarith only [h28355, h28359, h28374, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28376 | h28376
                      · linarith only [h16915, h28371, h28376, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28378 | h28378
                        · linarith only [h0, h26804, h28356, h28371, h28378, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c | h28380c
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h0, hlam, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h14396, hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h16915, hlam, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h18815, hlam, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h26804, hc01, hc24, hlam, hphi, ht12, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h20408, hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h26804, hlam, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h27373, hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h20408, h28355, h28359, h28378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h20408, h28355, h28359, h28378, hc02, hc45, hlam, hphi, ht23, ht34, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h20408, h28355, h28359, h28378, hc04, hc45, hlam, hphi, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h27731, hlam, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h16915, h28358, h28359, h28378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h0, h16915, h28358, h28359, h28378, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h27730, hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h28353, hlam, p28380_0]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h27373, h28357, hc01, hc12, hlam, hphi, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h0, h27373, h28357, hc01, hc12, hlam, hphi, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h27730, h27731, h28378, hc34, hc45, hlam, hphi, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [h16915, h27373, h28357, hc01, hc12, hlam, hphi, p28380_1]
                          · have p28380_0 := h28380c.1
                            have p28380_1 := h28380c.2.1
                            have p28380_2 := h28380c.2.2.1
                            have p28380_3 := h28380c.2.2.2
                            linarith only [hlam, p28380_0]
                  · linarith only [h14396, h27730, h28359, h28373, hc23, hc35, hlam, hphi]
            · linarith only [h27730, h27731, h28358, hc13, hc35, hlam, hphi]
          · linarith only [h0, h20408, h28355, h28357, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h28355, h28356, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28410 | h28410
        · linarith only [h0, h26804, h28355, h28410, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28412 | h28412
          · linarith only [h0, h27373, h28355, h28412, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28414 | h28414
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28415 | h28415
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28416 | h28416
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28417 | h28417
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28418 | h28418
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28419 | h28419
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28420 | h28420
                        · linarith only [h0, h26804, h27730, h27731, h28353, h28355, h28415, h28420, hc01, hc23, hlam, hphi, ht12]
                        · rcases h0bigk with h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c | h28422c
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h0, hlam, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h14396, hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h16915, hlam, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h18815, hlam, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h0, h28412, h28417, h28419, hc01, hc23, hlam, hphi, ht12, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h20408, hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h26804, hlam, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27373, hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27731, h28416, h28420, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27731, h28416, h28420, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27731, hlam, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27730, h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h0, h27730, h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27730, hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h28353, hlam, p28422_0]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h0, h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h27730, h27731, h28416, h28420, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [h16915, h27731, h28416, h28420, hc01, hc14, hlam, hphi, p28422_1]
                          · have p28422_0 := h28422c.1
                            have p28422_1 := h28422c.2.1
                            have p28422_2 := h28422c.2.2.1
                            have p28422_3 := h28422c.2.2.2
                            linarith only [hlam, p28422_0]
                      · linarith only [h28410, h28416, h28419, hlam]
                    · linarith only [h28355, h28415, h28418, hlam]
                  · linarith only [h14396, h27730, h28355, h28417, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28451 | h28451
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28452 | h28452
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28453 | h28453
                      · linarith only [h0, h28410, h28416, h28453, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h28410, h28453, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h28355, h28415, h28452, hc01, hc15, hlam, hphi]
                  · linarith only [h27730, h27731, h28355, h28415, h28451, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28458 | h28458
                · linarith only [h26804, h28353, h28414, h28415, h28458, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28460 | h28460
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28461 | h28461
                    · linarith only [h14396, h28415, h28461, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h28355, h28461, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h27730, h28355, h28460, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h14396, h27730, h28414, hlam]

end R2N4
