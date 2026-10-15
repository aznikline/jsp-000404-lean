import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h809 | h809
  · linarith only [h0, h1, h809, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h811 | h811
    · rcases m.htr 0 2 5 (by decide) (by decide) with h812 | h812
      · rcases m.htr 0 3 4 (by decide) (by decide) with h813 | h813
        · rcases m.htr 0 3 5 (by decide) (by decide) with h814 | h814
          · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
            · linarith only [h809, h815, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
              · rcases m.htr 1 2 5 (by decide) (by decide) with h818 | h818
                · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h820 | h820
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h821 | h821
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h823 | h823
                          · linarith only [h0, h1, h815, h817, h823, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h825 | h825
                            · linarith only [h821, h823, h825, hlam]
                            · rcases h2bigk with h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c | h827c
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h818, h821, h823, hc34, hlam, hphi, ht0b, ht45, ht5b, p827_1, u0elo1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h809, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h831 | h831
                                · rcases p827_3 (m.d 1 2) (by simp) with h832 | h832
                                  · linarith only [h0, h832, hlam]
                                  · linarith only [h817, h832, hlam]
                                · linarith only [h831, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h836 | h836
                                · rcases p827_3 (m.d 1 2) (by simp) with h837 | h837
                                  · linarith only [h0, h837, hlam]
                                  · linarith only [h818, h837, hlam]
                                · linarith only [h836, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, hlam, p827_1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h815, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h1, h815, h821, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p827_1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h1, h815, h821, h823, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p827_1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p827_1, u0ehi6]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                rcases p827_3 (m.d 0 2) (by simp) with h847 | h847
                                · linarith only [h809, h847, hlam]
                                · linarith only [h0, h847, hlam]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h1, h815, h817, hlam, p827_2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h1, h815, h818, hlam, p827_2]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h811, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h817, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h821, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h823, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h812, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h818, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h822, hlam, p827_0]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [h0, h1, h815, h818, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p827_1]
                              · have p827_0 := h827c.1
                                have p827_1 := h827c.2.1
                                have p827_2 := h827c.2.2.1
                                have p827_3 := h827c.2.2.2
                                linarith only [hlam, p827_0]
                        · linarith only [h0, h1, h815, h822, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h815, h821, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h812, h820, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h0, h1, h812, h819, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h0, h812, h817, h818, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h0, h1, h811, h815, h817, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h812, h814, hlam]
        · linarith only [h0, h1, h811, h813, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h871 | h871
        · rcases m.htr 0 3 5 (by decide) (by decide) with h872 | h872
          · rcases m.htr 1 2 3 (by decide) (by decide) with h873 | h873
            · linarith only [h809, h873, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
              · rcases m.htr 1 2 5 (by decide) (by decide) with h876 | h876
                · linarith only [h0, h811, h812, h876, hlam, hphi, u0ehi8, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h879 | h879
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h880 | h880
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h881 | h881
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h882 | h882
                          · linarith only [h0, h1, h873, h875, h882, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h884 | h884
                            · linarith only [h0, h1, h811, h812, h873, h875, h880, h882, h884, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                            · rcases h2bigk with h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h812, h882, hc12, hc45, hlam, hphi, ht23, ht34, p886_1]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h809, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h812, h880, h882, hc34, hc45, hlam, hphi, p886_1]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h812, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h0, hlam, p886_1]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h873, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h0, h1, h811, h812, h873, h880, h882, hc23, hc34, hc45, hlam, hphi, ht01, ht12, p886_1, u0ehi8]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h876, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h811, hc23, hlam, hphi, ht01, ht12, p886_1, u0ehi8]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                rcases p886_3 (m.d 0 2) (by simp) with h898 | h898
                                · linarith only [h809, h898, hlam]
                                · linarith only [h0, h898, hlam]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h0, h1, h873, h875, hlam, p886_2]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h811, h812, hc23, hlam, hphi, ht01, ht12, p886_1, u0ehi8]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h811, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h875, hlam, p886_0]
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
                                linarith only [h882, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h811, h882, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p886_1, u0ehi8]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h875, h882, hc24, hc45, hlam, hphi, p886_1]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [h881, hlam, p886_0]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                rcases p886_3 (m.d 0 2) (by simp) with h912 | h912
                                · linarith only [h812, h912, hlam]
                                · linarith only [h811, h912, hlam]
                              · have p886_0 := h886c.1
                                have p886_1 := h886c.2.1
                                have p886_2 := h886c.2.2.1
                                have p886_3 := h886c.2.2.2
                                linarith only [hlam, p886_0]
                        · linarith only [h0, h1, h873, h875, h879, h880, h881, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h873, h875, h880, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h872, h875, h879, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1, h875, h878, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h1, h811, h873, h875, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h921 | h921
            · linarith only [h0, h1, h872, h921, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
              · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
                · linarith only [h0, h1, h812, h872, h924, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h926 | h926
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h927 | h927
                    · linarith only [h0, h1, h872, h921, h927, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h923, h927, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h923, h926, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h811, h812, h923, hc12, hc25, hlam, hphi]
        · linarith only [h0, h1, h811, h871, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h933 | h933
      · rcases m.htr 0 3 4 (by decide) (by decide) with h934 | h934
        · rcases m.htr 0 3 5 (by decide) (by decide) with h935 | h935
          · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
            · linarith only [h0, h809, h936, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
              · linarith only [h0, h1, h811, h933, h936, h938, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h940 | h940
                · rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h942 | h942
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h943 | h943
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h944 | h944
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h945 | h945
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
                            · rcases h2bigk with h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h811, hc12, hc24, hlam, hphi, p947_1]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h809, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h811, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                rcases p947_3 (m.d 0 2) (by simp) with h952 | h952
                                · rcases p947_3 (m.d 1 2) (by simp) with h953 | h953
                                  · linarith only [h0, h953, hlam]
                                  · linarith only [h940, h953, hlam]
                                · linarith only [h952, hlam, p947_0]
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
                                linarith only [h936, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h938, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h0, h944, h946, hc45, hlam, hphi, ht0b, ht5b, p947_1, u0elo0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p947_1, u0ehi6]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                rcases p947_3 (m.d 0 2) (by simp) with h963 | h963
                                · linarith only [h809, h963, hlam]
                                · linarith only [h0, h963, hlam]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h811, h933, hc23, hlam, hphi, ht01, ht12, p947_1, u0ehi9]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h0, h1, h936, h940, hlam, p947_2]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h933, hc24, hlam, hphi, ht01, ht12, p947_1, u0ehi9]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                rcases p947_3 (m.d 0 2) (by simp) with h970 | h970
                                · linarith only [h811, h970, hlam]
                                · linarith only [h0, h970, hlam]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h943, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                rcases p947_3 (m.d 0 2) (by simp) with h975 | h975
                                · linarith only [h811, h975, hlam]
                                · linarith only [h933, h975, hlam]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h933, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h940, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h944, hlam, p947_0]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [h945, hlam, p947_1]
                              · have p947_0 := h947c.1
                                have p947_1 := h947c.2.1
                                have p947_2 := h947c.2.2.1
                                have p947_3 := h947c.2.2.2
                                linarith only [hlam, p947_0]
                            · linarith only [h0, h1, h936, h940, h945, h946, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h811, h933, h945, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                        · linarith only [h0, h1, h936, h944, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h936, h943, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h933, h942, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h0, h1, h933, h941, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h0, h1, h933, h936, h940, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h933, h935, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h991 | h991
          · rcases m.htr 1 2 3 (by decide) (by decide) with h992 | h992
            · linarith only [h0, h1, h934, h992, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h994 | h994
              · linarith only [h0, h1, h811, h934, h994, hc02, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h996 | h996
                · rcases m.htr 1 3 4 (by decide) (by decide) with h997 | h997
                  · linarith only [h0, h1, h934, h992, h997, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h933, h997, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h811, h933, h996, hc12, hc24, hlam, hphi]
          · linarith only [h0, h1, h933, h991, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1002 | h1002
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1003 | h1003
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
            · linarith only [h0, h1004, h809, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
              · linarith only [h0, h1006, h811, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1008 | h1008
                · linarith only [h0, h1, h1004, h1008, h933, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1011 | h1011
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1012 | h1012
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
                            · rcases h2bigk with h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1014, h933, hc12, hc24, hlam, hphi, p1016_1]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h809, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h811, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h933, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h0, hlam, p1016_1]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1004, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1006, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1008, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                rcases p1016_3 (m.d 0 2) (by simp) with h1028 | h1028
                                · linarith only [h1028, h809, hlam]
                                · linarith only [h0, h1028, hlam]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h811, hc23, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h933, hc23, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                rcases p1016_3 (m.d 0 2) (by simp) with h1035 | h1035
                                · linarith only [h1035, h811, hlam]
                                · linarith only [h0, h1035, hlam]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1012, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1012, h933, hc23, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p1016_1, u0ehi6]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                rcases p1016_3 (m.d 0 2) (by simp) with h1042 | h1042
                                · linarith only [h1042, h933, hlam]
                                · linarith only [h0, h1042, hlam]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1013, hlam, p1016_0]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [h1014, hlam, p1016_1]
                              · have p1016_0 := h1016c.1
                                have p1016_1 := h1016c.2.1
                                have p1016_2 := h1016c.2.2.1
                                have p1016_3 := h1016c.2.2.2
                                linarith only [hlam, p1016_0]
                            · rcases h2bigk with h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h0, h1, h1004, hc12, hc23, hlam, hphi, p1048_1]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h809, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h811, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h933, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h0, hlam, p1048_1]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1004, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1006, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1008, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hc23, hlam, hphi, ht01, ht12, p1048_1, u0ehi6]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                rcases p1048_3 (m.d 0 2) (by simp) with h1060 | h1060
                                · linarith only [h1060, h809, hlam]
                                · linarith only [h0, h1060, hlam]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1014, h1015, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1048_1]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h933, hc23, hlam, hphi, ht01, ht12, p1048_1, u0ehi6]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht12, p1048_1, u0ehi6]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                rcases p1048_3 (m.d 0 2) (by simp) with h1067 | h1067
                                · linarith only [h1067, h811, hlam]
                                · linarith only [h0, h1067, hlam]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1012, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1012, h933, hc23, hlam, hphi, ht01, ht12, p1048_1, u0ehi6]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hc25, hlam, hphi, ht01, ht12, p1048_1, u0ehi6]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                rcases p1048_3 (m.d 0 2) (by simp) with h1074 | h1074
                                · linarith only [h1074, h933, hlam]
                                · linarith only [h0, h1074, hlam]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1013, hlam, p1048_0]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [h1014, hlam, p1048_1]
                              · have p1048_0 := h1048c.1
                                have p1048_1 := h1048c.2.1
                                have p1048_2 := h1048c.2.2.1
                                have p1048_3 := h1048c.2.2.2
                                linarith only [hlam, p1048_0]
                          · linarith only [h1014, h811, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · linarith only [h1, h1004, h1013, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h0, h1, h1004, h1012, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h0, h1, h1003, h1011, hlam, hphi, u0ehi6, u0elo2]
                  · linarith only [h0, h1, h1002, h1010, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1085 | h1085
            · linarith only [h0, h1, h1003, h1085, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
              · linarith only [h0, h1, h1003, h1087, h811, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
                · linarith only [h0, h1, h1003, h1089, h933, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1091 | h1091
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
                    · linarith only [h0, h1, h1003, h1085, h1092, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1092, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h1, h1002, h1091, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1096 | h1096
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1097 | h1097
            · linarith only [h0, h1, h1002, h1097, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
              · linarith only [h0, h1, h1002, h1099, h811, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
                · linarith only [h0, h1, h1002, h1101, h933, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1103 | h1103
                  · linarith only [h0, h1, h1002, h1097, h1103, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1103, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
            · linarith only [h0, h1, h1096, h1106, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1108 | h1108
              · linarith only [h0, h1, h1096, h1108, h811, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1110 | h1110
                · linarith only [h0, h1, h1096, h1110, h933, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                  · linarith only [h0, h1, h1002, h1106, h1112, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1112, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]

set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x0_x0 m hb0 hb2 hb3 h0 h1
  · exact r1l7_20_12_13_M_LR_L_I_L_I_x0_x1 m hb0 hb2 hb3 h0 h1

end R2N4
