import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h722 | h722
  · rcases m.htr 0 2 5 (by decide) (by decide) with h723 | h723
    · rcases m.htr 0 3 4 (by decide) (by decide) with h724 | h724
      · rcases m.htr 0 3 5 (by decide) (by decide) with h725 | h725
        · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
          · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
            · linarith only [h4, h727, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h729 | h729
              · rcases m.htr 1 2 5 (by decide) (by decide) with h730 | h730
                · rcases m.htr 1 3 5 (by decide) (by decide) with h731 | h731
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h732 | h732
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h733 | h733
                      · linarith only [h0, h4, h729, h733, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · linarith only [h4, h722, h726, h732, h733, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h0, h4, h724, h730, h732, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4, h725, h727, h729, h731, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h723, h729, h730, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · linarith only [h4, h722, h729, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
            · linarith only [h4, h740, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h742 | h742
              · rcases m.htr 1 2 5 (by decide) (by decide) with h743 | h743
                · rcases m.htr 1 3 5 (by decide) (by decide) with h744 | h744
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                      · linarith only [h0, h2, h4, h726, h742, h746, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h748 | h748
                        · linarith only [h2, h726, h742, h745, h748, hlam]
                        · rcases h0bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h0, h743, h746, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h1, h740, h743, h745, h746, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            rcases p750_3 (m.d 0 1) (by simp) with h754 | h754
                            · rcases p750_3 (m.d 0 2) (by simp) with h755 | h755
                              · linarith only [h0, h755, hlam]
                              · linarith only [h722, h755, hlam]
                            · linarith only [h2, h754, hlam]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            rcases p750_3 (m.d 0 1) (by simp) with h759 | h759
                            · rcases p750_3 (m.d 0 2) (by simp) with h760 | h760
                              · linarith only [h0, h760, hlam]
                              · linarith only [h723, h760, hlam]
                            · linarith only [h3, h759, hlam]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h0, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h4, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h2, h4, h742, h745, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p750_1, u2elo2]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p750_1, u2elo2]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h1, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h0, h743, h745, h746, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h2, h4, h742, h745, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p750_1, u2elo2]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h4, h723, h745, h746, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p750_1, u2elo2]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h2, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h722, hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h724, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h726, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h3, hlam, p750_1]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h723, hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h725, hlam, p750_0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [h2, h723, h742, h745, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p750_1, u2elo0]
                          · have p750_0 := h750c.1
                            have p750_1 := h750c.2.1
                            have p750_2 := h750c.2.2.1
                            have p750_3 := h750c.2.2.2
                            linarith only [hlam, p750_0]
                    · linarith only [h4, h724, h745, hlam]
                  · linarith only [h4, h725, h740, h742, h744, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h723, h742, h743, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h722, h742, hc12, hlam, hphi, u2elo2]
        · linarith only [h4, h723, h725, hlam]
      · linarith only [h4, h722, h724, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h790 | h790
      · rcases m.htr 0 3 5 (by decide) (by decide) with h791 | h791
        · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
          · linarith only [h722, h723, h792, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h794 | h794
            · linarith only [h4, h794, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h796 | h796
              · rcases m.htr 1 2 5 (by decide) (by decide) with h797 | h797
                · linarith only [h0, h723, h797, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h801 | h801
                      · linarith only [h0, h2, h4, h792, h796, h801, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h803 | h803
                        · linarith only [h0, h723, h796, h800, h801, h803, hlam]
                        · rcases h0bigk with h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c | h805c
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h0, h796, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h0, h723, h791, h796, h800, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            rcases p805_3 (m.d 0 1) (by simp) with h809 | h809
                            · rcases p805_3 (m.d 0 2) (by simp) with h810 | h810
                              · linarith only [h0, h810, hlam]
                              · linarith only [h722, h810, hlam]
                            · linarith only [h2, h809, hlam]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h0, h723, h796, h800, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h0, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h4, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h2, h4, h796, h800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo2]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h723, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h1, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h4, hc02, hlam, hphi, p805_1, u2elo2]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h2, h4, h796, h800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo2]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h4, h722, h723, h800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo2]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h2, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h722, hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h790, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h792, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h3, hlam, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h722, h800, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p805_1]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h791, hlam, p805_0]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [h2, h723, h796, h800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p805_1, u2elo4]
                          · have p805_0 := h805c.1
                            have p805_1 := h805c.2.1
                            have p805_2 := h805c.2.2.1
                            have p805_3 := h805c.2.2.2
                            linarith only [hlam, p805_0]
                    · linarith only [h4, h790, h800, hlam]
                  · linarith only [h4, h791, h794, h796, h799, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h722, h796, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h838 | h838
          · linarith only [h4, h722, h791, h838, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h840 | h840
            · linarith only [h4, h840, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h842 | h842
              · rcases m.htr 1 2 5 (by decide) (by decide) with h843 | h843
                · linarith only [h0, h723, h843, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h845 | h845
                  · linarith only [h0, h1, h4, h791, h842, h845, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h847 | h847
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                      · linarith only [h0, h2, h4, h838, h842, h848, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                        · linarith only [h723, h847, h848, h850, hc02, hlam, hphi, u2elo3]
                        · rcases h0bigk with h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c | h852c
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [hlam, p852_0]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h0, h842, h847, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h0, h4, h842, h847, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            rcases p852_3 (m.d 0 1) (by simp) with h856 | h856
                            · rcases p852_3 (m.d 0 2) (by simp) with h857 | h857
                              · linarith only [h0, h857, hlam]
                              · linarith only [h722, h857, hlam]
                            · linarith only [h2, h856, hlam]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h0, h4, h791, h842, h847, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h0, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [hlam, p852_0]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h4, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h2, h4, h842, h847, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1, u2elo2]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h723, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h1, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h791, hc02, hc35, hlam, hphi, ht23, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [hlam, p852_0]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h2, h791, h842, h847, h850, hc34, hc45, hlam, hphi, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h791, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h2, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h722, hlam, p852_0]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h790, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [hlam, p852_0]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h838, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h3, hlam, p852_1]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h0, h723, h842, h847, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1, u2elo4]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h723, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p852_1, u2elo4]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [h2, h723, h842, h847, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p852_1, u2elo4]
                          · have p852_0 := h852c.1
                            have p852_1 := h852c.2.1
                            have p852_2 := h852c.2.2.1
                            have p852_3 := h852c.2.2.2
                            linarith only [hlam, p852_0]
                    · linarith only [h4, h790, h847, hlam]
              · linarith only [h4, h722, h842, hc12, hlam, hphi, u2elo2]
      · linarith only [h4, h722, h790, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h885 | h885
    · rcases m.htr 0 3 4 (by decide) (by decide) with h886 | h886
      · rcases m.htr 0 3 5 (by decide) (by decide) with h887 | h887
        · rcases m.htr 0 4 5 (by decide) (by decide) with h888 | h888
          · rcases m.htr 1 2 3 (by decide) (by decide) with h889 | h889
            · linarith only [h4, h889, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h891 | h891
              · linarith only [h0, h722, h891, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
                · rcases m.htr 1 3 5 (by decide) (by decide) with h894 | h894
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h895 | h895
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h897 | h897
                        · rcases h0bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h893, h896, hc01, hc45, hlam, hphi, ht0b, ht5b, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h886, h897, hc01, hc45, hlam, hphi, ht0b, ht5b, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h722, h893, h896, hc01, hc45, hlam, hphi, ht0b, ht5b, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            rcases p898_3 (m.d 0 1) (by simp) with h903 | h903
                            · rcases p898_3 (m.d 0 2) (by simp) with h904 | h904
                              · linarith only [h0, h904, hlam]
                              · linarith only [h885, h904, hlam]
                            · linarith only [h3, h903, hlam]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h4, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h722, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h3, h722, h895, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p898_1, u2elo2]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h1, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h4, hc02, hlam, hphi, p898_1, u2elo2]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h4, h722, h893, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p898_1, u2elo2]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h3, h4, h894, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p898_1, u2elo2]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h2, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h0, h893, hc04, hc25, hlam, hphi, ht0b, ht5b, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h886, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h3, h722, h894, h895, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p898_1, u2elo2]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h3, hlam, p898_1]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h885, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h887, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [h888, hlam, p898_0]
                          · have p898_0 := h898c.1
                            have p898_1 := h898c.2.1
                            have p898_2 := h898c.2.2.1
                            have p898_3 := h898c.2.2.2
                            linarith only [hlam, p898_0]
                        · linarith only [h0, h4, h893, h896, h897, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h722, h885, h888, h896, hlam]
                    · linarith only [h4, h886, h895, hlam]
                  · linarith only [h4, h885, h887, h889, h893, h894, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h4, h885, h893, hc12, hlam, hphi, u2elo2]
          · linarith only [h722, h885, h888, hlam]
        · linarith only [h4, h885, h887, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h935 | h935
        · rcases m.htr 0 4 5 (by decide) (by decide) with h936 | h936
          · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
            · linarith only [h4, h937, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h939 | h939
              · linarith only [h0, h722, h939, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
                · rcases m.htr 1 3 5 (by decide) (by decide) with h942 | h942
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h943 | h943
                    · linarith only [h4, h886, h943, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h945 | h945
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
                        · rcases h0bigk with h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, h941, h945, hc01, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, h4, h941, h945, hc01, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, h4, h886, h941, h945, hc01, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            rcases p947_3 (m.d 0 1) (by simp) with h952 | h952
                            · rcases p947_3 (m.d 0 2) (by simp) with h953 | h953
                              · linarith only [h0, h953, hlam]
                              · linarith only [h885, h953, hlam]
                            · linarith only [h3, h952, hlam]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h4, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h722, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo2]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h1, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, h886, h941, h945, hc04, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h886, hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h3, h4, h941, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo2]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h2, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h0, h722, h941, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h722, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p947_1, u2elo3]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h3, h722, h941, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h3, hlam, p947_1]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h885, hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h935, hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [h936, hlam, p947_0]
                          · have p947_0 := h947c.1
                            have p947_1 := h947c.2.1
                            have p947_2 := h947c.2.2.1
                            have p947_3 := h947c.2.2.2
                            linarith only [hlam, p947_0]
                        · linarith only [h0, h4, h941, h943, h945, h946, hlam]
                      · linarith only [h722, h936, h945, hlam]
                  · linarith only [h4, h935, h937, h942, hc12, hlam, hphi, u2elo2]
                · linarith only [h885, h941, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, h885, h886, h936, hlam]
        · linarith only [h4, h885, h935, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h983 | h983
      · rcases m.htr 0 3 5 (by decide) (by decide) with h984 | h984
        · rcases m.htr 0 4 5 (by decide) (by decide) with h985 | h985
          · rcases m.htr 1 2 3 (by decide) (by decide) with h986 | h986
            · linarith only [h4, h986, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h988 | h988
              · linarith only [h0, h722, h988, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h990 | h990
                · linarith only [h0, h885, h990, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h992 | h992
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h993 | h993
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h994 | h994
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                        · rcases h0bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            rcases p996_3 (m.d 0 1) (by simp) with h998 | h998
                            · rcases p996_3 (m.d 0 2) (by simp) with h999 | h999
                              · linarith only [h0, h999, hlam]
                              · rcases p996_3 (m.d 0 3) (by simp) with h1001 | h1001
                                · linarith only [h1, h1001, hlam]
                                · linarith only [h1001, h4, hlam]
                            · linarith only [h0, h998, hlam]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h983, h995, hc01, hc45, hlam, hphi, ht0b, ht5b, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h983, h995, hc01, hc45, hlam, hphi, ht0b, ht5b, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            rcases p996_3 (m.d 0 1) (by simp) with h1007 | h1007
                            · rcases p996_3 (m.d 0 2) (by simp) with h1008 | h1008
                              · linarith only [h0, h1008, hlam]
                              · rcases p996_3 (m.d 0 3) (by simp) with h1010 | h1010
                                · linarith only [h1, h1010, hlam]
                                · linarith only [h1010, h984, hlam]
                            · linarith only [h1007, h3, hlam]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h4, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h722, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h885, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h1, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p996_1, u2elo2]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h4, h983, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p996_1, u2elo2]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, h4, h885, hc12, hlam, hphi, p996_1, u2elo2]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h2, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, h722, hc12, hlam, hphi, p996_1, u2elo3]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h983, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, h4, h885, h983, hc12, hlam, hphi, p996_1, u2elo2]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h3, hlam, p996_1]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h0, h885, hc12, hlam, hphi, p996_1, u2elo4]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h984, hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [h985, hlam, p996_0]
                          · have p996_0 := h996c.1
                            have p996_1 := h996c.2.1
                            have p996_2 := h996c.2.2.1
                            have p996_3 := h996c.2.2.2
                            linarith only [hlam, p996_0]
                        · rcases h0bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            rcases p1034_3 (m.d 0 1) (by simp) with h1036 | h1036
                            · rcases p1034_3 (m.d 0 2) (by simp) with h1037 | h1037
                              · linarith only [h0, h1037, hlam]
                              · rcases p1034_3 (m.d 0 3) (by simp) with h1039 | h1039
                                · linarith only [h1, h1039, hlam]
                                · linarith only [h1039, h4, hlam]
                            · linarith only [h0, h1036, hlam]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1, h992, h995, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h985, h995, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h985, h995, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h4, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h722, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h885, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h1, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h4, h985, h995, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, h4, h885, hc12, hlam, hphi, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h2, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, h722, h993, hc12, hlam, hphi, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h983, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, h722, h885, h993, hc12, hlam, hphi, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h3, hlam, p1034_1]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h0, h885, h993, h994, hc12, hlam, hphi, p1034_1, u2elo2]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h984, hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [h985, hlam, p1034_0]
                          · have p1034_0 := h1034c.1
                            have p1034_1 := h1034c.2.1
                            have p1034_2 := h1034c.2.2.1
                            have p1034_3 := h1034c.2.2.2
                            linarith only [hlam, p1034_0]
                      · linarith only [h722, h985, h994, hlam]
                    · linarith only [h4, h983, h993, hlam]
                  · linarith only [h4, h984, h986, h992, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1069 | h1069
            · linarith only [h0, h1069, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1071 | h1071
              · linarith only [h0, h1071, h722, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
                · linarith only [h0, h1073, h885, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1075 | h1075
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1076 | h1076
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1077 | h1077
                      · linarith only [h1076, h1077, h722, h985, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1079 | h1079
                        · linarith only [h1077, h1079, h4, h983, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases h0bigk with h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [hlam, p1081_0]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            rcases p1081_3 (m.d 0 1) (by simp) with h1083 | h1083
                            · rcases p1081_3 (m.d 0 2) (by simp) with h1084 | h1084
                              · linarith only [h0, h1084, hlam]
                              · rcases p1081_3 (m.d 0 3) (by simp) with h1086 | h1086
                                · linarith only [h1, h1086, hlam]
                                · linarith only [h1086, h4, hlam]
                            · linarith only [h0, h1083, hlam]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h1, h1075, h1079, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            rcases p1081_3 (m.d 0 1) (by simp) with h1091 | h1091
                            · rcases p1081_3 (m.d 0 2) (by simp) with h1092 | h1092
                              · linarith only [h0, h1092, hlam]
                              · rcases p1081_3 (m.d 0 3) (by simp) with h1094 | h1094
                                · linarith only [h1, h1094, hlam]
                                · linarith only [h1094, h983, hlam]
                            · linarith only [h1091, h2, hlam]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            rcases p1081_3 (m.d 0 1) (by simp) with h1098 | h1098
                            · rcases p1081_3 (m.d 0 2) (by simp) with h1099 | h1099
                              · linarith only [h0, h1099, hlam]
                              · rcases p1081_3 (m.d 0 3) (by simp) with h1101 | h1101
                                · linarith only [h1, h1101, hlam]
                                · linarith only [h1101, h984, hlam]
                            · linarith only [h1098, h3, hlam]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [hlam, p1081_0]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h4, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h722, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h885, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h1, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1081_1, u2elo2]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [hlam, p1081_0]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, h4, h722, hc12, hlam, hphi, p1081_1, u2elo2]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, h4, h722, h985, hc12, hlam, hphi, p1081_1, u2elo2]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h2, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, h722, hc12, hlam, hphi, p1081_1, u2elo3]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h983, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [hlam, p1081_0]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h985, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h3, hlam, p1081_1]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h0, h885, hc12, hlam, hphi, p1081_1, u2elo4]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h984, hlam, p1081_0]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [h4, h984, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1081_1, u2elo2]
                          · have p1081_0 := h1081c.1
                            have p1081_1 := h1081c.2.1
                            have p1081_2 := h1081c.2.2.1
                            have p1081_3 := h1081c.2.2.2
                            linarith only [hlam, p1081_0]
                    · linarith only [h1076, h4, h983, hlam]
                  · linarith only [h1069, h1075, h4, h984, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1127 | h1127
          · linarith only [h1127, h983, h984, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1129 | h1129
            · linarith only [h0, h1129, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1131 | h1131
              · linarith only [h0, h1131, h722, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                · linarith only [h0, h1133, h885, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1135 | h1135
                  · linarith only [h1, h1135, h983, h984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1137 | h1137
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1138 | h1138
                      · linarith only [h1127, h1131, h1137, h1138, h2, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1140 | h1140
                        · linarith only [h1138, h1140, h983, h984, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h0bigk with h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c | h1142c
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [hlam, p1142_0]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            rcases p1142_3 (m.d 0 1) (by simp) with h1144 | h1144
                            · rcases p1142_3 (m.d 0 2) (by simp) with h1145 | h1145
                              · linarith only [h0, h1145, hlam]
                              · rcases p1142_3 (m.d 0 3) (by simp) with h1147 | h1147
                                · linarith only [h1, h1147, hlam]
                                · linarith only [h1147, h4, hlam]
                            · linarith only [h0, h1144, hlam]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h983, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            rcases p1142_3 (m.d 0 1) (by simp) with h1152 | h1152
                            · rcases p1142_3 (m.d 0 2) (by simp) with h1153 | h1153
                              · linarith only [h0, h1153, hlam]
                              · rcases p1142_3 (m.d 0 3) (by simp) with h1155 | h1155
                                · linarith only [h1, h1155, hlam]
                                · linarith only [h1155, h983, hlam]
                            · linarith only [h1152, h2, hlam]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h983, h984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h0, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [hlam, p1142_0]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h4, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h722, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h885, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h1, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h0, h984, hc12, hc35, hlam, hphi, ht23, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [hlam, p1142_0]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h1131, h2, h984, hc12, hc35, hlam, hphi, ht23, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h984, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h2, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h0, h722, hc12, hlam, hphi, p1142_1, u2elo3]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h983, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [hlam, p1142_0]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h1127, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h3, hlam, p1142_1]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h0, h885, hc12, hlam, hphi, p1142_1, u2elo4]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h885, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1142_1, u2elo4]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [h1131, h2, h885, hc12, hlam, hphi, p1142_1, u2elo4]
                          · have p1142_0 := h1142c.1
                            have p1142_1 := h1142c.2.1
                            have p1142_2 := h1142c.2.2.1
                            have p1142_3 := h1142c.2.2.2
                            linarith only [hlam, p1142_0]
                    · linarith only [h1137, h4, h983, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1181 | h1181
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1182 | h1182
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1183 | h1183
            · linarith only [h0, h1183, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1185 | h1185
              · linarith only [h0, h1182, h1185, h4, h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1187 | h1187
                · linarith only [h0, h1187, h885, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1189 | h1189
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1190 | h1190
                    · linarith only [h1, h1187, h1189, h1190, h983, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1193 | h1193
                        · rcases h0bigk with h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            rcases p1194_3 (m.d 0 1) (by simp) with h1196 | h1196
                            · rcases p1194_3 (m.d 0 2) (by simp) with h1197 | h1197
                              · linarith only [h0, h1197, hlam]
                              · rcases p1194_3 (m.d 0 3) (by simp) with h1199 | h1199
                                · linarith only [h1, h1199, hlam]
                                · linarith only [h1199, h4, hlam]
                            · linarith only [h0, h1196, hlam]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h1, h1189, h1193, hc01, hc45, hlam, hphi, ht0b, ht5b, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h1, h1189, h1193, h983, hc01, hc45, hlam, hphi, ht0b, ht5b, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            rcases p1194_3 (m.d 0 1) (by simp) with h1205 | h1205
                            · rcases p1194_3 (m.d 0 2) (by simp) with h1206 | h1206
                              · linarith only [h0, h1206, hlam]
                              · rcases p1194_3 (m.d 0 3) (by simp) with h1208 | h1208
                                · linarith only [h1, h1208, hlam]
                                · linarith only [h1181, h1208, hlam]
                            · linarith only [h1205, h3, hlam]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h4, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h722, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h885, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h1, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1194_1, u2elo2]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h983, hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, h1190, h4, h885, hc12, hlam, hphi, p1194_1, u2elo3]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h2, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, h722, hc12, hlam, hphi, p1194_1, u2elo3]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h722, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1194_1, u2elo3]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, h722, h885, hc12, hlam, hphi, p1194_1, u2elo3]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h3, hlam, p1194_1]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h0, h885, hc12, hlam, hphi, p1194_1, u2elo4]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h1181, hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [h1182, hlam, p1194_0]
                          · have p1194_0 := h1194c.1
                            have p1194_1 := h1194c.2.1
                            have p1194_2 := h1194c.2.2.1
                            have p1194_3 := h1194c.2.2.2
                            linarith only [hlam, p1194_0]
                        · linarith only [h0, h1190, h1193, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1182, h1192, h722, hlam]
                  · linarith only [h1181, h1189, h983, hc13, hc34, hlam, hphi]
          · linarith only [h1181, h1182, h983, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1236 | h1236
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1237 | h1237
            · linarith only [h0, h1237, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1239 | h1239
              · linarith only [h0, h1236, h1239, h4, h722, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1241 | h1241
                · linarith only [h0, h1241, h885, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h1, h1181, h1243, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
                    · linarith only [h1245, h4, h983, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1247 | h1247
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1248 | h1248
                        · rcases h0bigk with h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            rcases p1249_3 (m.d 0 1) (by simp) with h1251 | h1251
                            · rcases p1249_3 (m.d 0 2) (by simp) with h1252 | h1252
                              · linarith only [h0, h1252, hlam]
                              · rcases p1249_3 (m.d 0 3) (by simp) with h1254 | h1254
                                · linarith only [h1, h1254, hlam]
                                · linarith only [h1254, h4, hlam]
                            · linarith only [h0, h1251, hlam]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            rcases p1249_3 (m.d 0 1) (by simp) with h1258 | h1258
                            · rcases p1249_3 (m.d 0 2) (by simp) with h1259 | h1259
                              · linarith only [h0, h1259, hlam]
                              · rcases p1249_3 (m.d 0 3) (by simp) with h1261 | h1261
                                · linarith only [h1, h1261, hlam]
                                · rcases p1249_3 (m.d 0 4) (by simp) with h1263 | h1263
                                  · linarith only [h1263, h2, hlam]
                                  · linarith only [h1263, h983, hlam]
                            · linarith only [h1, h1258, hlam]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1236, hc01, hc45, hlam, hphi, ht0b, ht5b, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            rcases p1249_3 (m.d 0 1) (by simp) with h1268 | h1268
                            · rcases p1249_3 (m.d 0 2) (by simp) with h1269 | h1269
                              · linarith only [h0, h1269, hlam]
                              · rcases p1249_3 (m.d 0 3) (by simp) with h1271 | h1271
                                · linarith only [h1, h1271, hlam]
                                · rcases p1249_3 (m.d 0 4) (by simp) with h1273 | h1273
                                  · linarith only [h1273, h2, hlam]
                                  · linarith only [h1236, h1273, hlam]
                            · linarith only [h1268, h3, hlam]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h0, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h4, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h722, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h885, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h0, h1181, hc12, hc35, hlam, hphi, ht23, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h983, hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1181, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h2, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h0, h722, hc12, hlam, hphi, p1249_1, u2elo3]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h722, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1249_1, u2elo3]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1, h1181, h1237, h722, hc12, hlam, hphi, p1249_1, u2elo3]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h3, hlam, p1249_1]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h0, h885, hc12, hlam, hphi, p1249_1, u2elo4]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1, h1237, h885, hc12, hlam, hphi, p1249_1, u2elo4]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [h1236, hlam, p1249_0]
                          · have p1249_0 := h1249c.1
                            have p1249_1 := h1249c.2.1
                            have p1249_2 := h1249c.2.2.1
                            have p1249_3 := h1249c.2.2.2
                            linarith only [hlam, p1249_0]
                        · linarith only [h0, h1245, h1248, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1236, h1247, h722, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
            · linarith only [h0, h1299, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1301 | h1301
              · linarith only [h0, h1301, h722, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1303 | h1303
                · linarith only [h1236, h1301, h1303, h2, h885, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
                  · linarith only [h1, h1181, h1305, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1307 | h1307
                    · linarith only [h0, h1307, h4, h983, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1309 | h1309
                      · linarith only [h0, h1236, h1309, h4, h983, hc12, hlam, hphi, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1311 | h1311
                        · linarith only [h0, h1309, h1311, h722, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1307, h1311, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_H_I_L_0_x0_x0_x0_x0_x0 m hb0 hb2 h0 h1 h2 h3 h4
  · exact r1l7_20_12_H_I_L_0_x0_x0_x0_x0_x1 m hb0 hb2 h0 h1 h2 h3 h4

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1314 | h1314
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1315 | h1315
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1316 | h1316
      · linarith only [h0, h1316, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1318 | h1318
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1319 | h1319
          · linarith only [h1, h1319, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1321 | h1321
            · linarith only [h1321, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1323 | h1323
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1324 | h1324
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1325 | h1325
                  · linarith only [h1316, h1325, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1323, h1325, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h1315, h1323, h1324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h1314, h1316, h1323, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1330 | h1330
          · linarith only [h0, h1315, h1318, h1330, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1332 | h1332
            · linarith only [h0, h1315, h1332, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1335 | h1335
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h0, h1315, h1316, h1318, h1336, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1336, h3, hc12, hlam, hphi, u2elo4]
                · linarith only [h1315, h1316, h1334, h1335, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1314, h1316, h1334, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1341 | h1341
      · linarith only [h0, h1315, h1341, h3, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1343 | h1343
        · linarith only [h1314, h1315, h1343, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1345 | h1345
          · linarith only [h1314, h1315, h1345, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1347 | h1347
            · linarith only [h1347, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1349 | h1349
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1350 | h1350
                · linarith only [h0, h1315, h1350, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
                  · linarith only [h0, h1315, h1341, h1352, h2, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h1349, h1350, h1352, h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1314, h1315, h1349, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1356 | h1356
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1357 | h1357
      · linarith only [h0, h1314, h1357, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1359 | h1359
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1360 | h1360
          · linarith only [h1, h1360, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1362 | h1362
            · linarith only [h1, h1314, h1356, h1362, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1364 | h1364
              · linarith only [h1314, h1364, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1366 | h1366
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
                  · linarith only [h1, h1357, h1364, h1367, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1366, h1367, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1314, h1356, h1366, hc12, hlam, hphi, u2elo2]
        · linarith only [h1314, h1356, h1359, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1372 | h1372
      · linarith only [h0, h1314, h1372, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1374 | h1374
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1375 | h1375
          · linarith only [h1, h1375, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1377 | h1377
            · linarith only [h1, h1374, h1377, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1379 | h1379
              · linarith only [h1314, h1379, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1381 | h1381
                · linarith only [h1, h1356, h1379, h1381, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1383 | h1383
                  · linarith only [h0, h1314, h1372, h1383, h3, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1, h1379, h1383, h3, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1386 | h1386
          · linarith only [h1374, h1386, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1388 | h1388
            · linarith only [h1388, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
              · linarith only [h0, h1314, h1390, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
                · linarith only [h0, h1356, h1392, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
                  · linarith only [h0, h1372, h1394, hlam]
                  · linarith only [h1, h1390, h1394, h3, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_H_I_L_0_x0_x0_x0_x0 m hb0 hb2 h0 h1 h2 h3
  · exact r1l7_20_12_H_I_L_0_x0_x0_x0_x1 m hb0 hb2 h0 h1 h2 h3

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1397 | h1397
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1398 | h1398
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1399 | h1399
      · linarith only [h0, h1399, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1401 | h1401
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1402 | h1402
          · linarith only [h0, h1398, h1402, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1404 | h1404
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1405 | h1405
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1407 | h1407
                  · linarith only [h0, h1399, h1407, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1406, h1407, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1398, h1406, hc12, hlam, hphi, u2elo0]
              · linarith only [h1, h1404, h1405, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1412 | h1412
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                  · linarith only [h0, h1399, h1414, h2, hlam]
                  · linarith only [h0, h1413, h1414, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1398, h1413, hc12, hlam, hphi, u2elo0]
              · linarith only [h0, h1401, h1412, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1419 | h1419
          · linarith only [h1, h1419, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1421 | h1421
            · linarith only [h1398, h1401, h1421, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1423 | h1423
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1424 | h1424
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h0, h1399, h1425, h2, hlam]
                  · linarith only [h0, h1424, h1425, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1398, h1401, h1424, hc12, hlam, hphi, u2elo4]
              · linarith only [h1397, h1423, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1430 | h1430
      · linarith only [h0, h1398, h1430, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1432 | h1432
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1433 | h1433
          · linarith only [h1, h1433, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1435 | h1435
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1436 | h1436
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1437 | h1437
                · linarith only [h1398, h1437, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1439 | h1439
                  · linarith only [h1, h1430, h1432, h1437, h1439, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1439, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1398, h1432, h1436, h2, hc12, hlam, hphi, u2elo2]
            · linarith only [h1398, h1432, h1435, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1444 | h1444
          · linarith only [h1, h1444, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1446 | h1446
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1447 | h1447
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1448 | h1448
                · linarith only [h0, h1398, h1448, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1450 | h1450
                  · linarith only [h0, h1430, h1450, h2, hlam]
                  · linarith only [h1, h1448, h1450, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1446, h1447, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1454 | h1454
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1455 | h1455
                · linarith only [h1398, h1455, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
                  · linarith only [h0, h1430, h1457, h2, hlam]
                  · linarith only [h1, h1455, h1457, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1397, h1454, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1461 | h1461
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1462 | h1462
      · linarith only [h0, h1462, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1464 | h1464
        · linarith only [h0, h1397, h1464, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
          · linarith only [h0, h1461, h1466, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
            · linarith only [h0, h1397, h1461, h1468, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1472 | h1472
                  · linarith only [h0, h1462, h1472, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1471, h1472, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1397, h1461, h1462, h1470, h1471, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
                · linarith only [h0, h1470, h1476, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1461, h1462, h1476, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1479 | h1479
      · linarith only [h0, h1461, h1479, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1481 | h1481
        · linarith only [h1, h1397, h1461, h1481, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1483 | h1483
          · linarith only [h1, h1483, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1485 | h1485
            · linarith only [h1, h1397, h1485, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1487 | h1487
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
                · linarith only [h1461, h1488, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1490 | h1490
                  · linarith only [h1, h1479, h1488, h1490, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1490, h2, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1493 | h1493
                · linarith only [h0, h1461, h1493, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1495 | h1495
                  · linarith only [h1, h1487, h1493, h1495, h2, hc24, hc45, hlam, hphi]
                  · linarith only [h1, h1493, h1495, h2, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_H_I_L_0_x0_x0_x0 m hb0 hb2 h0 h1 h2
  · exact r1l7_20_12_H_I_L_0_x0_x0_x1 m hb0 hb2 h0 h1 h2

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1498 | h1498
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1499 | h1499
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1500 | h1500
      · linarith only [h0, h1, h1500, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1502 | h1502
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1503 | h1503
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1504 | h1504
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1505 | h1505
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1506 | h1506
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1507 | h1507
                  · linarith only [h0, h1, h1500, h1507, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1507, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1510 | h1510
                  · linarith only [h0, h1, h1500, h1510, hlam]
                  · linarith only [h0, h1, h1510, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h1503, h1505, hlam]
            · linarith only [h1, h1498, h1504, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1515 | h1515
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1516 | h1516
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1517 | h1517
                · linarith only [h1502, h1503, h1517, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1519 | h1519
                  · linarith only [h1500, h1519, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1, h1519, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1499, h1516, hlam]
            · linarith only [h1, h1499, h1502, h1503, h1515, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1524 | h1524
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1525 | h1525
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1526 | h1526
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1527 | h1527
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
                  · linarith only [h0, h1, h1500, h1528, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1528, hc12, hlam, hphi, u2elo2]
                · linarith only [h1502, h1524, h1527, hlam]
              · linarith only [h0, h1, h1524, h1526, hlam]
            · linarith only [h1, h1498, h1525, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1534 | h1534
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1535 | h1535
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1536 | h1536
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1537 | h1537
                  · linarith only [h0, h1, h1500, h1537, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1537, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                  · linarith only [h0, h1, h1500, h1540, hlam]
                  · linarith only [h0, h1, h1540, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1499, h1535, hlam]
            · linarith only [h1, h1498, h1534, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1545 | h1545
      · linarith only [h0, h1, h1545, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1547 | h1547
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1548 | h1548
          · linarith only [h0, h1499, h1548, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1550 | h1550
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1551 | h1551
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1552 | h1552
                · linarith only [h0, h1499, h1547, h1552, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h0, h1, h1545, h1554, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1554, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1557 | h1557
                · linarith only [h0, h1, h1547, h1551, h1557, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1559 | h1559
                  · linarith only [h0, h1, h1551, h1559, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1559, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h1545, h1547, h1550, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1563 | h1563
          · linarith only [h1498, h1499, h1547, h1563, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1565 | h1565
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1566 | h1566
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1567 | h1567
                · linarith only [h1498, h1499, h1567, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1569 | h1569
                  · linarith only [h0, h1, h1545, h1569, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1569, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1572 | h1572
                · linarith only [h1, h1498, h1566, h1572, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1574 | h1574
                  · linarith only [h0, h1, h1566, h1574, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1574, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1498, h1565, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1578 | h1578
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1579 | h1579
      · linarith only [h0, h1, h1579, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1581 | h1581
        · linarith only [h0, h1498, h1581, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1583 | h1583
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1584 | h1584
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1585 | h1585
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                  · linarith only [h0, h1, h1579, h1587, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1587, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1498, h1583, h1586, hlam]
              · linarith only [h0, h1, h1579, h1583, h1585, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1592 | h1592
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1593 | h1593
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1594 | h1594
                  · linarith only [h0, h1, h1579, h1594, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1594, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h1578, h1584, h1593, hlam]
              · linarith only [h0, h1, h1583, h1592, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1602 | h1602
                  · linarith only [h1579, h1602, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1, h1602, hc12, hlam, hphi, u2elo2]
                · linarith only [h1498, h1578, h1601, hlam]
              · linarith only [h1498, h1578, h1599, h1600, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1607 | h1607
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1608 | h1608
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1609 | h1609
                  · linarith only [h0, h1, h1599, h1609, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1609, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h1578, h1599, h1608, hlam]
              · linarith only [h1, h1578, h1607, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1614 | h1614
      · linarith only [h0, h1, h1614, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1616 | h1616
        · linarith only [h0, h1498, h1616, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1618 | h1618
          · linarith only [h0, h1578, h1618, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1620 | h1620
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1621 | h1621
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1622 | h1622
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1623 | h1623
                  · linarith only [h0, h1, h1614, h1623, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1623, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1626 | h1626
                  · linarith only [h0, h1, h1614, h1620, h1626, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h1626, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
                · linarith only [h1620, h1621, h1629, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1631 | h1631
                  · linarith only [h0, h1498, h1620, h1621, h1631, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1631, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1634 | h1634
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1635 | h1635
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1636 | h1636
                  · linarith only [h0, h1578, h1620, h1634, h1636, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1636, hc12, hlam, hphi, u2elo2]
                · linarith only [h1620, h1634, h1635, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1640 | h1640
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
                  · linarith only [h0, h1, h1620, h1641, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1641, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1644 | h1644
                  · linarith only [h0, h1, h1620, h1644, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1644, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_H_I_L_0_x0_x0 m hb0 hb2 h0 h1
  · exact r1l7_20_12_H_I_L_0_x0_x1 m hb0 hb2 h0 h1

end R2N4
