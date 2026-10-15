import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S9

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_14_M_LR_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h697 | h697
  · rcases m.htr 0 2 3 (by decide) (by decide) with h698 | h698
    · rcases m.htr 0 2 4 (by decide) (by decide) with h699 | h699
      · rcases m.htr 0 3 4 (by decide) (by decide) with h700 | h700
        · rcases m.htr 0 4 5 (by decide) (by decide) with h701 | h701
          · rcases m.htr 1 2 3 (by decide) (by decide) with h702 | h702
            · rcases m.htr 1 2 4 (by decide) (by decide) with h703 | h703
              · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h706 | h706
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                      · linarith only [h698, h705, h707, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h0, h697, h704, h707, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h697, h704, h706, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h711 | h711
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h712 | h712
                      · rcases h4bigk with h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, h703, h711, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, h711, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, h705, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          rcases p713_3 (m.d 0 4) (by simp) with h718 | h718
                          · rcases p713_3 (m.d 1 4) (by simp) with h719 | h719
                            · linarith only [h697, h719, hlam]
                            · linarith only [h704, h719, hlam]
                          · linarith only [h718, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h697, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, h711, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, h705, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h0, h697, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h699, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h703, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h705, hlam, p713_1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h699, hc45, hlam, hphi, ht0b, ht5b, p713_1, u0elo1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h700, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h698, h700, hc14, hlam, hphi, ht0b, ht45, ht5b, p713_1, u0elo1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h698, h700, hc24, hlam, hphi, ht0b, ht45, ht5b, p713_1, u0elo1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h698, h700, hc45, hlam, hphi, ht0b, ht5b, p713_1, u0elo1]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h701, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h704, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h711, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [h712, hlam, p713_0]
                        · have p713_0 := h713c.1
                          have p713_1 := h713c.2.1
                          have p713_2 := h713c.2.2.1
                          have p713_3 := h713c.2.2.2
                          linarith only [hlam, p713_0]
                      · linarith only [h0, h697, h703, h711, h712, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h697, h704, h711, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h746 | h746
                    · linarith only [h699, h704, h746, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h748 | h748
                      · linarith only [h703, h704, h745, h748, hlam]
                      · rcases h4bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          rcases p750_3 (m.d 0 4) (by simp) with h752 | h752
                          · rcases p750_3 (m.d 1 4) (by simp) with h753 | h753
                            · linarith only [h697, h753, hlam]
                            · rcases p750_3 (m.d 2 4) (by simp) with h755 | h755
                              · linarith only [h699, h755, hlam]
                              · rcases p750_3 (m.d 3 4) (by simp) with h757 | h757
                                · linarith only [h700, h757, hlam]
                                · rcases p750_3 (m.d 4 5) (by simp) with h759 | h759
                                  · linarith only [h701, h759, hlam]
                                  · linarith only [h704, h759, hlam]
                          · linarith only [h697, h752, hlam]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          rcases p750_3 (m.d 0 4) (by simp) with h763 | h763
                          · rcases p750_3 (m.d 1 4) (by simp) with h764 | h764
                            · linarith only [h697, h764, hlam]
                            · linarith only [h703, h764, hlam]
                          · linarith only [h699, h763, hlam]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          rcases p750_3 (m.d 0 4) (by simp) with h768 | h768
                          · rcases p750_3 (m.d 1 4) (by simp) with h769 | h769
                            · linarith only [h697, h769, hlam]
                            · linarith only [h703, h745, h769, hlam]
                          · linarith only [h700, h768, hlam]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h697, h703, h704, h745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h697, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h704, h745, hc34, hc45, hlam, hphi, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h697, h701, h704, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h704, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h699, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h703, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h699, hc34, hlam, hphi, ht0b, ht45, ht5b, p750_1, u0elo1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h746, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h700, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h698, h745, hc14, hlam, hphi, ht0b, ht45, ht5b, p750_1, u0elo1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h745, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h748, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h701, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h697, h701, h703, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h697, h701, h745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h697, h701, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h794 | h794
                    · linarith only [h703, h704, h794, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h796 | h796
                      · linarith only [h698, h700, h704, h796, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h697, h701, h745, h796, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h703, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h697, h701, h702, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h801 | h801
            · rcases m.htr 1 2 4 (by decide) (by decide) with h802 | h802
              · rcases m.htr 1 4 5 (by decide) (by decide) with h803 | h803
                · linarith only [h697, h701, h803, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h805 | h805
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h806 | h806
                    · linarith only [h0, h697, h701, h802, h806, hc12, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h808 | h808
                      · linarith only [h698, h701, h805, h808, hlam, hphi, u0ehi8, u0elo1]
                      · rcases h4bigk with h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c | h810c
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h701, h802, hc24, hc45, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h701, hc24, hc45, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h701, hc34, hc45, hlam, hphi, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h701, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h697, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, h697, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h0, h697, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p810_1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h803, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h699, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h802, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h699, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1, u0elo1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h806, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h700, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h698, h700, hc14, hlam, hphi, ht0b, ht45, ht5b, p810_1, u0elo1]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h805, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [h808, hlam, p810_0]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p810_1, u0ehi8]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 4) (by simp) with h832 | h832
                          · linarith only [h701, h832, hlam]
                          · linarith only [h697, h832, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 4) (by simp) with h835 | h835
                          · linarith only [h701, h835, hlam]
                          · linarith only [h699, h835, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          rcases p810_3 (m.d 0 4) (by simp) with h838 | h838
                          · linarith only [h701, h838, hlam]
                          · linarith only [h700, h838, hlam]
                        · have p810_0 := h810c.1
                          have p810_1 := h810c.2.1
                          have p810_2 := h810c.2.2.1
                          have p810_3 := h810c.2.2.2
                          linarith only [hlam, p810_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h842 | h842
                    · linarith only [h701, h802, h842, hc14, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h844 | h844
                      · linarith only [h698, h700, h701, h844, hlam, hphi, u0ehi8, u0elo1]
                      · rcases h4bigk with h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c | h846c
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h701, h802, hc24, hc45, hlam, hphi, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h701, hc24, hc45, hlam, hphi, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h701, h805, hc23, hc45, hlam, hphi, ht34, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h701, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h697, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h0, h697, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h0, h697, h805, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h803, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h699, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h802, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h805, hlam, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h842, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h700, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h698, h700, hc14, hlam, hphi, ht0b, ht45, ht5b, p846_1, u0elo1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h698, h700, h805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p846_1, u0elo1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h844, hlam, p846_0]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p846_1, u0ehi8]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          rcases p846_3 (m.d 0 4) (by simp) with h868 | h868
                          · linarith only [h701, h868, hlam]
                          · linarith only [h697, h868, hlam]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          rcases p846_3 (m.d 0 4) (by simp) with h871 | h871
                          · linarith only [h701, h871, hlam]
                          · linarith only [h699, h871, hlam]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [h805, hc23, hc45, hlam, hphi, ht34, p846_1]
                        · have p846_0 := h846c.1
                          have p846_1 := h846c.2.1
                          have p846_2 := h846c.2.2.1
                          have p846_3 := h846c.2.2.2
                          linarith only [hlam, p846_0]
              · linarith only [h0, h802, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h697, h801, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h878 | h878
          · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
            · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
              · rcases m.htr 1 4 5 (by decide) (by decide) with h881 | h881
                · rcases m.htr 2 3 4 (by decide) (by decide) with h882 | h882
                  · linarith only [h698, h700, h882, hlam, hphi, u0ehi7, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h884 | h884
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h885 | h885
                      · rcases h4bigk with h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h697, h880, h884, hc45, hlam, hphi, ht0b, ht5b, p886_1, u0elo0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, h697, h884, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h700, hlam, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 4) (by simp) with h891 | h891
                          · rcases p886_3 (m.d 1 4) (by simp) with h892 | h892
                            · linarith only [h697, h892, hlam]
                            · linarith only [h881, h892, hlam]
                          · linarith only [h891, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h697, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, h697, h884, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, h697, h700, hc12, hlam, hphi, ht01, p886_1, u0ehi7]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h0, h697, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h699, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h880, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h882, hlam, p886_1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h699, hc45, hlam, hphi, ht0b, ht5b, p886_1, u0elo1]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p886_1, u0ehi8]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 4) (by simp) with h907 | h907
                          · linarith only [h700, h907, hlam]
                          · linarith only [h697, h907, hlam]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 4) (by simp) with h910 | h910
                          · linarith only [h700, h910, hlam]
                          · linarith only [h699, h910, hlam]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          rcases p886_3 (m.d 0 4) (by simp) with h914 | h914
                          · linarith only [h700, h914, hlam]
                          · linarith only [h878, h914, hlam]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h878, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h881, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h884, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [h885, hlam, p886_0]
                        · have p886_0 := h886c.1
                          have p886_1 := h886c.2.1
                          have p886_2 := h886c.2.2.1
                          have p886_3 := h886c.2.2.2
                          linarith only [hlam, p886_0]
                      · linarith only [h700, h885, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h0, h697, h881, h882, h884, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h924 | h924
                  · linarith only [h700, h924, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                    · linarith only [h880, h881, h926, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                      · rcases h4bigk with h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 4) (by simp) with h931 | h931
                          · rcases p929_3 (m.d 1 4) (by simp) with h932 | h932
                            · linarith only [h697, h932, hlam]
                            · rcases p929_3 (m.d 2 4) (by simp) with h934 | h934
                              · linarith only [h699, h934, hlam]
                              · rcases p929_3 (m.d 3 4) (by simp) with h936 | h936
                                · rcases p929_3 (m.d 4 5) (by simp) with h937 | h937
                                  · linarith only [h878, h937, hlam]
                                  · linarith only [h881, h937, hlam]
                                · linarith only [h700, h878, h881, h936, hlam, hphi, u0ehi7, u0elo3]
                          · linarith only [h697, h931, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 4) (by simp) with h942 | h942
                          · rcases p929_3 (m.d 1 4) (by simp) with h943 | h943
                            · linarith only [h697, h943, hlam]
                            · linarith only [h880, h943, hlam]
                          · linarith only [h699, h942, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h700, hlam, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h0, h697, h881, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h697, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h881, h924, h928, hc23, hc35, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h0, h697, h700, h878, h881, hc12, hlam, hphi, ht01, p929_1, u0ehi7]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h881, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h699, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h880, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h924, hlam, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h926, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h878, h881, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 4) (by simp) with h960 | h960
                          · linarith only [h700, h960, hlam]
                          · linarith only [h697, h960, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 4) (by simp) with h963 | h963
                          · linarith only [h700, h963, hlam]
                          · linarith only [h699, h963, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h880, h881, h924, hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h878, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h878, h880, h924, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1, u0elo3]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h0, h697, h878, h924, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h928, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                      · linarith only [h0, h697, h700, h878, h928, hc12, hlam, hphi, ht01, u0ehi7]
              · linarith only [h0, h880, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h697, h700, h879, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
            · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
              · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
                · linarith only [h700, h878, h978, hc14, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
                  · linarith only [h698, h700, h980, hlam, hphi, u0ehi7, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h982 | h982
                    · linarith only [h697, h700, h878, h977, h982, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
                      · linarith only [h700, h878, h984, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h700, h984, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h977, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h697, h700, h976, hc23, hlam, hphi, ht01, ht12, u0ehi7]
      · linarith only [h0, h697, h699, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h990 | h990
      · rcases m.htr 0 3 4 (by decide) (by decide) with h991 | h991
        · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
          · rcases m.htr 1 2 3 (by decide) (by decide) with h993 | h993
            · linarith only [h0, h698, h993, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h697, h992, h993, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h996 | h996
            · linarith only [h0, h698, h996, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h697, h996, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · linarith only [h0, h697, h698, h991, hlam]
      · linarith only [h0, h697, h990, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1001 | h1001
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1002 | h1002
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1004 | h1004
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1007 | h1007
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1009 | h1009
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                      · linarith only [h1001, h1008, h1010, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h1001, h1008, h1009, h1010, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                      · linarith only [h1001, h1003, h1009, h1013, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases h4bigk with h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c | h1015c
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h697, hlam, p1015_1]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          rcases p1015_3 (m.d 0 4) (by simp) with h1018 | h1018
                          · rcases p1015_3 (m.d 1 4) (by simp) with h1019 | h1019
                            · rcases p1015_3 (m.d 2 4) (by simp) with h1020 | h1020
                              · linarith only [h1002, h1020, hlam]
                              · rcases p1015_3 (m.d 3 4) (by simp) with h1022 | h1022
                                · linarith only [h1003, h1022, hlam]
                                · rcases p1015_3 (m.d 4 5) (by simp) with h1024 | h1024
                                  · linarith only [h1004, h1024, hlam]
                                  · linarith only [h1009, h1024, hlam]
                            · linarith only [h1006, h1019, hlam]
                          · linarith only [h1002, h1018, hlam]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          rcases p1015_3 (m.d 0 4) (by simp) with h1029 | h1029
                          · rcases p1015_3 (m.d 1 4) (by simp) with h1030 | h1030
                            · rcases p1015_3 (m.d 2 4) (by simp) with h1031 | h1031
                              · linarith only [h1002, h1031, hlam]
                              · linarith only [h1008, h1031, hlam]
                            · linarith only [h1008, h1009, h1030, h697, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                          · linarith only [h1003, h1029, hlam]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1001, h1003, h1009, hc24, hlam, hphi, ht0b, ht45, ht5b, p1015_1, u0elo1]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1006, hc12, hlam, hphi, ht01, p1015_1, u0ehi8]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          rcases p1015_3 (m.d 0 4) (by simp) with h1039 | h1039
                          · linarith only [h1039, h697, hlam]
                          · linarith only [h1002, h1039, hlam]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          rcases p1015_3 (m.d 0 4) (by simp) with h1042 | h1042
                          · linarith only [h1042, h697, hlam]
                          · linarith only [h1003, h1042, hlam]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          rcases p1015_3 (m.d 0 4) (by simp) with h1045 | h1045
                          · linarith only [h1045, h697, hlam]
                          · linarith only [h1004, h1045, hlam]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1002, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1006, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1004, h1009, hc34, hlam, hphi, ht0b, ht45, ht5b, p1015_1, u0elo3]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1009, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1003, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h697, hc34, hlam, hphi, ht01, ht12, ht23, p1015_1, u0ehi5]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1008, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1013, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1004, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1007, hlam, p1015_0]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1001, h1003, h1004, hc24, hlam, hphi, ht0b, ht45, ht5b, p1015_1, u0elo1]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [h1001, h1003, h1004, hc34, hlam, hphi, ht0b, ht45, ht5b, p1015_1, u0elo1]
                        · have p1015_0 := h1015c.1
                          have p1015_1 := h1015c.2.1
                          have p1015_2 := h1015c.2.2.1
                          have p1015_3 := h1015c.2.2.2
                          linarith only [hlam, p1015_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                      · rcases h4bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h697, hlam, p1065_1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1001, h1003, h1063, hc45, hlam, hphi, ht0b, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1001, h1003, h1008, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          rcases p1065_3 (m.d 0 4) (by simp) with h1070 | h1070
                          · rcases p1065_3 (m.d 1 4) (by simp) with h1071 | h1071
                            · rcases p1065_3 (m.d 2 4) (by simp) with h1072 | h1072
                              · linarith only [h1002, h1072, hlam]
                              · linarith only [h1063, h1072, hlam]
                            · linarith only [h1007, h1071, hlam]
                          · linarith only [h1070, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, p1065_1, u0ehi8]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          rcases p1065_3 (m.d 0 4) (by simp) with h1079 | h1079
                          · linarith only [h1079, h697, hlam]
                          · linarith only [h1002, h1079, hlam]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          rcases p1065_3 (m.d 0 4) (by simp) with h1082 | h1082
                          · linarith only [h1082, h697, hlam]
                          · linarith only [h1003, h1082, hlam]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          rcases p1065_3 (m.d 0 4) (by simp) with h1085 | h1085
                          · linarith only [h1085, h697, hlam]
                          · linarith only [h1004, h1085, hlam]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1002, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1006, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1008, hlam, p1065_1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1002, hc45, hlam, hphi, ht0b, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1003, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1001, h1003, hc14, hlam, hphi, ht0b, ht45, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1001, h1003, hc24, hlam, hphi, ht0b, ht45, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1001, h1003, hc45, hlam, hphi, ht0b, ht5b, p1065_1, u0elo1]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1004, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1007, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1063, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [h1064, hlam, p1065_0]
                        · have p1065_0 := h1065c.1
                          have p1065_1 := h1065c.2.1
                          have p1065_2 := h1065c.2.2.1
                          have p1065_3 := h1065c.2.2.2
                          linarith only [hlam, p1065_0]
                      · linarith only [h1002, h1063, h1064, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1104 | h1104
                      · linarith only [h1001, h1003, h1008, h1063, h1104, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1004, h1008, h1104, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1001, h1003, h1004, h1007, h697, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1006, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1005, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1110 | h1110
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1111 | h1111
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1112 | h1112
                · linarith only [h1004, h1111, h1112, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h1112, h697, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
              · linarith only [h0, h1002, h1111, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1001, h1110, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1121 | h1121
                  · linarith only [h1001, h1003, h1121, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1123 | h1123
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1124 | h1124
                      · rcases h4bigk with h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h697, hlam, p1125_1]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1123, hc45, hlam, hphi, ht0b, ht5b, p1125_1, u0elo3]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1003, hlam, p1125_1]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          rcases p1125_3 (m.d 0 4) (by simp) with h1130 | h1130
                          · rcases p1125_3 (m.d 1 4) (by simp) with h1131 | h1131
                            · rcases p1125_3 (m.d 2 4) (by simp) with h1132 | h1132
                              · linarith only [h1002, h1132, hlam]
                              · linarith only [h1123, h1132, hlam]
                            · linarith only [h1120, h1131, hlam]
                          · linarith only [h1130, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1119, hc12, hlam, hphi, ht01, p1125_1, u0ehi8]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          rcases p1125_3 (m.d 0 4) (by simp) with h1139 | h1139
                          · linarith only [h1139, h697, hlam]
                          · linarith only [h1002, h1139, hlam]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1003, h1119, hc12, hlam, hphi, ht01, p1125_1, u0ehi7]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          rcases p1125_3 (m.d 0 4) (by simp) with h1143 | h1143
                          · linarith only [h1143, h697, hlam]
                          · linarith only [h1117, h1143, hlam]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1002, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1119, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1121, hlam, p1125_1]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1002, hc45, hlam, hphi, ht0b, ht5b, p1125_1, u0elo1]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1117, hc34, hlam, hphi, ht01, ht12, ht23, p1125_1, u0ehi9]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h697, hc34, hlam, hphi, ht01, ht12, ht23, p1125_1, u0ehi5]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          rcases p1125_3 (m.d 0 4) (by simp) with h1153 | h1153
                          · linarith only [h1003, h1153, hlam]
                          · linarith only [h1002, h1153, hlam]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          rcases p1125_3 (m.d 0 4) (by simp) with h1157 | h1157
                          · linarith only [h1003, h1157, hlam]
                          · linarith only [h1117, h1157, hlam]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1117, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1120, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1123, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [h1124, hlam, p1125_0]
                        · have p1125_0 := h1125c.1
                          have p1125_1 := h1125c.2.1
                          have p1125_2 := h1125c.2.2.1
                          have p1125_3 := h1125c.2.2.2
                          linarith only [hlam, p1125_0]
                      · linarith only [h1002, h1123, h1124, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1166 | h1166
                      · rcases h4bigk with h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h697, hlam, p1167_1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          rcases p1167_3 (m.d 0 4) (by simp) with h1170 | h1170
                          · rcases p1167_3 (m.d 1 4) (by simp) with h1171 | h1171
                            · rcases p1167_3 (m.d 2 4) (by simp) with h1172 | h1172
                              · linarith only [h1002, h1172, hlam]
                              · rcases p1167_3 (m.d 3 4) (by simp) with h1174 | h1174
                                · rcases p1167_3 (m.d 4 5) (by simp) with h1175 | h1175
                                  · linarith only [h1117, h1175, hlam]
                                  · linarith only [h1123, h1175, hlam]
                                · linarith only [h1121, h1174, hlam]
                            · linarith only [h1119, h1171, hlam]
                          · linarith only [h1002, h1170, hlam]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1003, hlam, p1167_1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1121, h1123, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1167_1, u0elo3]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, p1167_1, u0ehi8]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          rcases p1167_3 (m.d 0 4) (by simp) with h1185 | h1185
                          · linarith only [h1185, h697, hlam]
                          · linarith only [h1002, h1185, hlam]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1003, hc14, hlam, hphi, ht01, p1167_1, u0ehi7]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          rcases p1167_3 (m.d 0 4) (by simp) with h1189 | h1189
                          · linarith only [h1189, h697, hlam]
                          · linarith only [h1117, h1189, hlam]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1002, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1119, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1121, hlam, p1167_1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1123, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1117, h1121, h1123, hc23, hc34, hlam, hphi, p1167_1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h697, hc34, hlam, hphi, ht01, ht12, ht23, p1167_1, u0ehi5]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          rcases p1167_3 (m.d 0 4) (by simp) with h1199 | h1199
                          · linarith only [h1003, h1199, hlam]
                          · linarith only [h1002, h1199, hlam]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1121, h1123, hc23, hc34, hlam, hphi, p1167_1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1117, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1120, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1002, h1117, h1121, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1167_1, u0elo1]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [h1166, hlam, p1167_0]
                        · have p1167_0 := h1167c.1
                          have p1167_1 := h1167c.2.1
                          have p1167_2 := h1167c.2.2.1
                          have p1167_3 := h1167c.2.2.2
                          linarith only [hlam, p1167_0]
                      · linarith only [h1002, h1003, h1117, h1166, hlam, hphi, u0ehi7, u0elo1]
                · linarith only [h1002, h1117, h1120, h697, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1119, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1118, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1215 | h1215
                · linarith only [h1117, h1214, h1215, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h1215, h697, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
              · linarith only [h0, h1002, h1214, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1001, h1213, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1220 | h1220
        · linarith only [h1001, h1002, h1220, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1222 | h1222
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1223 | h1223
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1224 | h1224
              · linarith only [h1002, h1224, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1224, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1001, h1223, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
              · linarith only [h1002, h1229, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1229, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1001, h1228, hlam, hphi, u0ehi5, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1233 | h1233
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1234 | h1234
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1235 | h1235
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1236 | h1236
            · linarith only [h1001, h1236, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h1236, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1239 | h1239
            · linarith only [h1001, h1233, h1239, h697, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1239, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h1001, h1233, h1234, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1243 | h1243
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1245 | h1245
            · linarith only [h1001, h1245, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h1245, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1248 | h1248
            · linarith only [h0, h1001, h1248, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1248, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1252 | h1252
            · linarith only [h0, h1001, h1252, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1252, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
            · linarith only [h0, h1001, h1255, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1255, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_14_M_LR_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_14_M_LR_L_I_x0 m hb0 hb4 h0
  · exact r1l7_20_14_M_LR_L_I_x1 m hb0 hb4 h0

end R2N4
