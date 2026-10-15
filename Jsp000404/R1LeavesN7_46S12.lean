import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h790 | h790
  · rcases m.htr 0 2 5 (by decide) (by decide) with h791 | h791
    · rcases m.htr 0 3 4 (by decide) (by decide) with h792 | h792
      · rcases m.htr 0 3 5 (by decide) (by decide) with h793 | h793
        · rcases m.htr 0 4 5 (by decide) (by decide) with h794 | h794
          · rcases m.htr 1 2 3 (by decide) (by decide) with h795 | h795
            · linarith only [h4, h795, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h797 | h797
              · rcases m.htr 1 3 4 (by decide) (by decide) with h798 | h798
                · rcases m.htr 1 3 5 (by decide) (by decide) with h799 | h799
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h801 | h801
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h802 | h802
                        · linarith only [h0, h4, h797, h802, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h4, h790, h794, h802, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h4, h792, h801, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h4, h790, h794, h800, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h4, h793, h795, h797, h799, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h792, h795, h797, h798, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h790, h797, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
            · linarith only [h4, h810, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h812 | h812
              · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                · rcases m.htr 1 3 5 (by decide) (by decide) with h814 | h814
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h815 | h815
                    · linarith only [h2, h794, h815, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
                        · linarith only [h2, h794, h812, h818, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h820 | h820
                          · linarith only [h2, h794, h812, h817, h820, hlam]
                          · rcases h0bigk with h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c | h822c
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, h812, hc24, hlam, hphi, ht0b, ht45, ht5b, p822_1, u0elo0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h1, h810, h812, h817, hc34, hlam, hphi, ht0b, ht45, ht5b, p822_1, u0elo0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 1) (by simp) with h826 | h826
                              · rcases p822_3 (m.d 0 2) (by simp) with h827 | h827
                                · linarith only [h0, h827, hlam]
                                · linarith only [h790, h827, hlam]
                              · linarith only [h2, h826, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 1) (by simp) with h831 | h831
                              · rcases p822_3 (m.d 0 2) (by simp) with h832 | h832
                                · linarith only [h0, h832, hlam]
                                · linarith only [h791, h832, hlam]
                              · linarith only [h3, h831, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h4, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h2, h4, h812, h817, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p822_1, u2elo2]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h2, h4, h794, h812, h817, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p822_1, u2elo2]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h1, hlam, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h0, h812, h817, hc34, hlam, hphi, ht0b, ht45, ht5b, p822_1, u0elo2]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 1) (by simp) with h844 | h844
                              · rcases p822_3 (m.d 0 2) (by simp) with h845 | h845
                                · linarith only [h4, h845, hlam]
                                · linarith only [h790, h845, hlam]
                              · linarith only [h2, h844, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              rcases p822_3 (m.d 0 1) (by simp) with h849 | h849
                              · rcases p822_3 (m.d 0 2) (by simp) with h850 | h850
                                · linarith only [h4, h850, hlam]
                                · linarith only [h791, h850, hlam]
                              · linarith only [h3, h849, hlam]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h2, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h790, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h792, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h794, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h3, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h791, hlam, p822_1]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h793, hlam, p822_0]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [h2, h4, h791, h812, h817, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p822_1, u2elo2]
                            · have p822_0 := h822c.1
                              have p822_1 := h822c.2.1
                              have p822_2 := h822c.2.2.1
                              have p822_3 := h822c.2.2.2
                              linarith only [hlam, p822_0]
                      · linarith only [h1, h4, h792, h817, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h4, h791, h793, h810, h812, h814, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h792, h810, h812, h813, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h790, h812, hc12, hlam, hphi, u2elo2]
        · linarith only [h4, h791, h793, hlam]
      · linarith only [h4, h790, h792, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h870 | h870
      · rcases m.htr 0 3 5 (by decide) (by decide) with h871 | h871
        · rcases m.htr 0 4 5 (by decide) (by decide) with h872 | h872
          · linarith only [h790, h791, h872, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
            · linarith only [h4, h874, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h876 | h876
              · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h879 | h879
                    · linarith only [h2, h872, h879, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h882 | h882
                        · linarith only [h0, h872, h876, h882, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h884 | h884
                          · linarith only [h0, h791, h876, h881, h882, h884, hlam]
                          · rcases h0bigk with h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c | h886c
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h0, h876, hc24, hlam, hphi, ht0b, ht45, ht5b, p886_1, u0elo0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h1, h874, h876, h881, hc34, hlam, hphi, ht0b, ht45, ht5b, p886_1, u0elo0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              rcases p886_3 (m.d 0 1) (by simp) with h890 | h890
                              · rcases p886_3 (m.d 0 2) (by simp) with h891 | h891
                                · linarith only [h0, h891, hlam]
                                · linarith only [h790, h891, hlam]
                              · linarith only [h2, h890, hlam]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h0, h791, h876, h881, hc34, hlam, hphi, ht0b, ht45, ht5b, p886_1, u0elo0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h0, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h4, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h2, h4, h876, h881, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p886_1, u2elo2]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h791, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h1, hlam, p886_1]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h4, hc02, hlam, hphi, p886_1, u2elo2]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              rcases p886_3 (m.d 0 1) (by simp) with h904 | h904
                              · rcases p886_3 (m.d 0 2) (by simp) with h905 | h905
                                · linarith only [h4, h905, hlam]
                                · linarith only [h790, h905, hlam]
                              · linarith only [h2, h904, hlam]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h0, h4, h791, h876, h881, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p886_1, u2elo2]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h2, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h790, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h870, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h872, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h3, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h0, h876, h881, hc34, hlam, hphi, ht0b, ht45, ht5b, p886_1, u0elo4]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [h871, hlam, p886_0]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              rcases p886_3 (m.d 0 1) (by simp) with h918 | h918
                              · rcases p886_3 (m.d 0 2) (by simp) with h919 | h919
                                · linarith only [h791, h919, hlam]
                                · linarith only [h790, h919, hlam]
                              · linarith only [h2, h918, hlam]
                            · have p886_0 := h886c.1
                              have p886_1 := h886c.2.1
                              have p886_2 := h886c.2.2.1
                              have p886_3 := h886c.2.2.2
                              linarith only [hlam, p886_0]
                      · linarith only [h4, h870, h881, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h4, h871, h874, h876, h878, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h870, h874, h876, h877, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h790, h876, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h928 | h928
          · linarith only [h4, h790, h871, h928, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h930 | h930
            · linarith only [h4, h930, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h932 | h932
              · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                · rcases m.htr 1 3 5 (by decide) (by decide) with h934 | h934
                  · linarith only [h0, h1, h4, h871, h932, h934, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h936 | h936
                    · linarith only [h2, h928, h936, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h939 | h939
                        · linarith only [h0, h928, h932, h939, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h941 | h941
                          · linarith only [h4, h790, h791, h871, h938, h939, h941, hlam]
                          · rcases h0bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h932, h938, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h4, h932, h938, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 1) (by simp) with h947 | h947
                              · rcases p943_3 (m.d 0 2) (by simp) with h948 | h948
                                · linarith only [h0, h948, hlam]
                                · linarith only [h790, h948, hlam]
                              · linarith only [h2, h947, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h4, h871, h932, h938, hc34, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h4, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h2, h791, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo4]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h791, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h1, hlam, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h871, h932, hc24, hlam, hphi, ht0b, ht45, ht5b, p943_1, u0elo4]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h790, h871, h938, h941, hc34, hc45, hlam, hphi, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h871, hlam, p943_1]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h2, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h790, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h870, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h928, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h3, hlam, p943_0]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h791, h932, h938, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo4]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [h0, h4, h791, h932, h938, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p943_1, u2elo4]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              rcases p943_3 (m.d 0 1) (by simp) with h971 | h971
                              · rcases p943_3 (m.d 0 2) (by simp) with h972 | h972
                                · linarith only [h791, h972, hlam]
                                · linarith only [h790, h972, hlam]
                              · linarith only [h2, h971, hlam]
                            · have p943_0 := h943c.1
                              have p943_1 := h943c.2.1
                              have p943_2 := h943c.2.2.1
                              have p943_3 := h943c.2.2.2
                              linarith only [hlam, p943_0]
                      · linarith only [h4, h870, h938, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h870, h871, h933, hc13, hc35, hlam, hphi]
              · linarith only [h4, h790, h932, hc12, hlam, hphi, u2elo2]
      · linarith only [h4, h790, h870, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h981 | h981
    · rcases m.htr 0 3 4 (by decide) (by decide) with h982 | h982
      · rcases m.htr 0 3 5 (by decide) (by decide) with h983 | h983
        · rcases m.htr 0 4 5 (by decide) (by decide) with h984 | h984
          · rcases m.htr 1 2 3 (by decide) (by decide) with h985 | h985
            · linarith only [h4, h985, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h987 | h987
              · linarith only [h0, h790, h987, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h989 | h989
                · rcases m.htr 1 3 5 (by decide) (by decide) with h990 | h990
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h993 | h993
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h994 | h994
                          · linarith only [h1, h989, h994, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h790, h981, h992, h993, h994, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · linarith only [h790, h982, h984, h993, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h4, h982, h992, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h790, h984, h987, h991, hc12, hlam, hphi, u2elo3]
                  · linarith only [h4, h983, h989, h990, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h982, h985, h989, hc12, hlam, hphi, u2elo2]
          · linarith only [h790, h981, h984, hlam]
        · linarith only [h4, h981, h983, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1004 | h1004
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1006 | h1006
            · linarith only [h0, h1006, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1008 | h1008
              · linarith only [h0, h1008, h790, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
                · linarith only [h1, h1010, h4, h982, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1012 | h1012
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1013 | h1013
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1014 | h1014
                      · linarith only [h1014, h4, h981, h982, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1016 | h1016
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1017 | h1017
                          · rcases h0bigk with h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c | h1018c
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1016, h981, hc45, hlam, hphi, ht0b, ht5b, p1018_1, u0elo0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1016, h4, h981, hc45, hlam, hphi, ht0b, ht5b, p1018_1, u0elo0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1016, h4, h981, h982, hc45, hlam, hphi, ht0b, ht5b, p1018_1, u0elo0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              rcases p1018_3 (m.d 0 1) (by simp) with h1023 | h1023
                              · rcases p1018_3 (m.d 0 2) (by simp) with h1024 | h1024
                                · linarith only [h0, h1024, hlam]
                                · linarith only [h1024, h981, hlam]
                              · linarith only [h1023, h3, hlam]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h0, hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h4, hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h790, hlam, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1014, h3, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1, hlam, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h0, h1014, h4, hc12, hc34, hlam, hphi, ht23, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h982, hlam, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              rcases p1018_3 (m.d 0 1) (by simp) with h1037 | h1037
                              · rcases p1018_3 (m.d 0 2) (by simp) with h1038 | h1038
                                · linarith only [h1038, h4, hlam]
                                · linarith only [h1038, h981, hlam]
                              · linarith only [h1037, h3, hlam]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h2, hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1016, h790, h981, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo3]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1016, h4, h790, h981, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1018_1, u2elo3]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              rcases p1018_3 (m.d 0 1) (by simp) with h1046 | h1046
                              · rcases p1018_3 (m.d 0 2) (by simp) with h1047 | h1047
                                · linarith only [h1047, h790, hlam]
                                · linarith only [h1047, h981, hlam]
                              · linarith only [h1046, h3, hlam]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h3, hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h981, hlam, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1004, hlam, p1018_0]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [h1005, hlam, p1018_1]
                            · have p1018_0 := h1018c.1
                              have p1018_1 := h1018c.2.1
                              have p1018_2 := h1018c.2.2.1
                              have p1018_3 := h1018c.2.2.2
                              linarith only [hlam, p1018_0]
                          · linarith only [h1014, h1016, h1017, h981, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1013, h1016, h3, h790, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1005, h1010, h1012, h1013, h4, h981, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h1004, h1006, h1012, h4, hc12, hlam, hphi, u2elo2]
          · linarith only [h1005, h4, h981, h982, hlam]
        · linarith only [h1004, h4, h981, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1062 | h1062
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1063 | h1063
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1064 | h1064
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1065 | h1065
            · linarith only [h0, h1065, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1067 | h1067
              · linarith only [h0, h1067, h790, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1070 | h1070
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1071 | h1071
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1072 | h1072
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1073 | h1073
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1074 | h1074
                          · linarith only [h1, h1069, h1074, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1071, h1074, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1069, h1071, h1073, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1062, h1072, h4, hlam]
                    · linarith only [h1062, h1064, h1067, h1071, h4, hc12, hlam, hphi, u2elo2]
                  · linarith only [h1063, h1065, h1070, h4, hc12, hlam, hphi, u2elo2]
                · linarith only [h1062, h1065, h1069, h4, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
            · linarith only [h0, h1062, h1082, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1084 | h1084
              · linarith only [h0, h1084, h790, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1086 | h1086
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1087 | h1087
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h1064, h1088, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1091 | h1091
                        · linarith only [h0, h1064, h1090, h1091, h790, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1093 | h1093
                          · linarith only [h1, h1086, h1091, h1093, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h0bigk with h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c | h1095c
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              rcases p1095_3 (m.d 0 1) (by simp) with h1097 | h1097
                              · rcases p1095_3 (m.d 0 2) (by simp) with h1098 | h1098
                                · linarith only [h0, h1098, hlam]
                                · rcases p1095_3 (m.d 0 3) (by simp) with h1100 | h1100
                                  · linarith only [h1, h1100, hlam]
                                  · linarith only [h1100, h4, hlam]
                              · linarith only [h0, h1097, hlam]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h1, h1087, h1093, hc34, hlam, hphi, ht0b, ht45, ht5b, p1095_1, u0elo0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              rcases p1095_3 (m.d 0 1) (by simp) with h1105 | h1105
                              · rcases p1095_3 (m.d 0 2) (by simp) with h1106 | h1106
                                · linarith only [h0, h1106, hlam]
                                · rcases p1095_3 (m.d 0 3) (by simp) with h1108 | h1108
                                  · linarith only [h1, h1108, hlam]
                                  · linarith only [h1062, h1108, hlam]
                              · linarith only [h1105, h2, hlam]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              rcases p1095_3 (m.d 0 1) (by simp) with h1112 | h1112
                              · rcases p1095_3 (m.d 0 2) (by simp) with h1113 | h1113
                                · linarith only [h0, h1113, hlam]
                                · rcases p1095_3 (m.d 0 3) (by simp) with h1115 | h1115
                                  · linarith only [h1, h1115, hlam]
                                  · linarith only [h1063, h1115, hlam]
                              · linarith only [h1112, h3, hlam]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h4, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h790, hlam, p1095_1]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h981, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h1, hlam, p1095_1]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1095_1, u2elo2]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h4, h790, hc12, hlam, hphi, p1095_1, u2elo2]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h1064, h4, h790, hc12, hlam, hphi, p1095_1, u2elo2]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h2, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h790, hc12, hlam, hphi, p1095_1, u2elo3]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h1062, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h1064, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h3, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h981, hc12, hlam, hphi, p1095_1, u2elo4]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h1063, hlam, p1095_0]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [h0, h1063, h4, h790, hc12, hlam, hphi, p1095_1, u2elo2]
                            · have p1095_0 := h1095c.1
                              have p1095_1 := h1095c.2.1
                              have p1095_2 := h1095c.2.2.1
                              have p1095_3 := h1095c.2.2.2
                              linarith only [hlam, p1095_0]
                      · linarith only [h0, h1062, h1090, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1063, h1086, h1087, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1062, h1082, h1086, h4, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
          · linarith only [h1062, h1063, h1142, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1144 | h1144
            · linarith only [h0, h1144, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1146 | h1146
              · linarith only [h0, h1146, h790, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1148 | h1148
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
                  · linarith only [h1, h1063, h1149, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1151 | h1151
                    · linarith only [h1142, h1151, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1153 | h1153
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1154 | h1154
                        · linarith only [h1142, h1153, h1154, h790, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1156 | h1156
                          · linarith only [h1148, h1149, h1154, h1156, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases h0bigk with h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              rcases p1158_3 (m.d 0 1) (by simp) with h1160 | h1160
                              · rcases p1158_3 (m.d 0 2) (by simp) with h1161 | h1161
                                · linarith only [h0, h1161, hlam]
                                · rcases p1158_3 (m.d 0 3) (by simp) with h1163 | h1163
                                  · linarith only [h1, h1163, hlam]
                                  · linarith only [h1163, h4, hlam]
                              · linarith only [h0, h1160, hlam]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1, h1148, hc34, hlam, hphi, ht0b, ht45, ht5b, p1158_1, u0elo0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              rcases p1158_3 (m.d 0 1) (by simp) with h1168 | h1168
                              · rcases p1158_3 (m.d 0 2) (by simp) with h1169 | h1169
                                · linarith only [h0, h1169, hlam]
                                · rcases p1158_3 (m.d 0 3) (by simp) with h1171 | h1171
                                  · linarith only [h1, h1171, hlam]
                                  · linarith only [h1062, h1171, hlam]
                              · linarith only [h1168, h2, hlam]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1, h1063, h1148, hc34, hlam, hphi, ht0b, ht45, ht5b, p1158_1, u0elo0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h0, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h4, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h790, hlam, p1158_1]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h981, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1, hlam, p1158_1]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h0, h1063, hc12, hc35, hlam, hphi, ht23, p1158_1]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h0, h1063, h790, h981, hc12, hlam, hphi, p1158_1, u2elo4]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1063, hlam, p1158_1]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h2, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h0, h790, hc12, hlam, hphi, p1158_1, u2elo3]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1062, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1142, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h3, hlam, p1158_0]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h0, h981, hc12, hlam, hphi, p1158_1, u2elo4]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1, h1148, h981, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1158_1, u2elo4]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [h1146, h2, h981, hc12, hlam, hphi, p1158_1, u2elo4]
                            · have p1158_0 := h1158c.1
                              have p1158_1 := h1158c.2.1
                              have p1158_2 := h1158c.2.2.1
                              have p1158_3 := h1158c.2.2.2
                              linarith only [hlam, p1158_0]
                      · linarith only [h1, h1148, h1153, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1062, h1063, h1148, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1198 | h1198
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1199 | h1199
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1200 | h1200
            · linarith only [h0, h1200, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1202 | h1202
              · linarith only [h0, h1199, h1202, h4, h790, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1204 | h1204
                · linarith only [h1, h1062, h1204, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1207 | h1207
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1208 | h1208
                      · linarith only [h1062, h1198, h1208, h981, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1210 | h1210
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1211 | h1211
                          · rcases h0bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              rcases p1212_3 (m.d 0 1) (by simp) with h1214 | h1214
                              · rcases p1212_3 (m.d 0 2) (by simp) with h1215 | h1215
                                · linarith only [h0, h1215, hlam]
                                · rcases p1212_3 (m.d 0 3) (by simp) with h1217 | h1217
                                  · linarith only [h1, h1217, hlam]
                                  · linarith only [h1217, h4, hlam]
                              · linarith only [h0, h1214, hlam]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1, h1206, h1211, hc45, hlam, hphi, ht0b, ht5b, p1212_1, u0elo0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1, h1062, h1206, h1211, hc45, hlam, hphi, ht0b, ht5b, p1212_1, u0elo0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              rcases p1212_3 (m.d 0 1) (by simp) with h1223 | h1223
                              · rcases p1212_3 (m.d 0 2) (by simp) with h1224 | h1224
                                · linarith only [h0, h1224, hlam]
                                · rcases p1212_3 (m.d 0 3) (by simp) with h1226 | h1226
                                  · linarith only [h1, h1226, hlam]
                                  · linarith only [h1198, h1226, hlam]
                              · linarith only [h1223, h3, hlam]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h4, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h790, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h981, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, h4, hc12, hlam, hphi, p1212_1, u2elo2]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1062, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, h1208, h4, h981, hc12, hlam, hphi, p1212_1, u2elo3]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h2, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, h790, hc12, hlam, hphi, p1212_1, u2elo3]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1, h1206, h1211, h790, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1212_1, u2elo3]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, h790, h981, hc12, hlam, hphi, p1212_1, u2elo3]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h3, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h0, h1210, h981, hc12, hlam, hphi, p1212_1, u2elo3]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1198, hlam, p1212_0]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [h1199, hlam, p1212_1]
                            · have p1212_0 := h1212c.1
                              have p1212_1 := h1212c.2.1
                              have p1212_2 := h1212c.2.2.1
                              have p1212_3 := h1212c.2.2.2
                              linarith only [hlam, p1212_0]
                          · linarith only [h1062, h1199, h1211, hlam]
                        · linarith only [h1207, h1210, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1199, h1202, h1207, h790, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1062, h1198, h1206, hc13, hc34, hlam, hphi]
          · linarith only [h1062, h1198, h1199, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1255 | h1255
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1256 | h1256
            · linarith only [h0, h1256, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1258 | h1258
              · linarith only [h0, h1255, h1258, h4, h790, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1260 | h1260
                · linarith only [h1, h1062, h1260, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1262 | h1262
                  · linarith only [h1, h1198, h1262, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1264 | h1264
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1265 | h1265
                      · linarith only [h1, h1062, h1256, h1265, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1267 | h1267
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1268 | h1268
                          · rcases h0bigk with h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              rcases p1269_3 (m.d 0 1) (by simp) with h1271 | h1271
                              · rcases p1269_3 (m.d 0 2) (by simp) with h1272 | h1272
                                · linarith only [h0, h1272, hlam]
                                · rcases p1269_3 (m.d 0 3) (by simp) with h1274 | h1274
                                  · linarith only [h1, h1274, hlam]
                                  · linarith only [h1274, h4, hlam]
                              · linarith only [h0, h1271, hlam]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              rcases p1269_3 (m.d 0 1) (by simp) with h1278 | h1278
                              · rcases p1269_3 (m.d 0 2) (by simp) with h1279 | h1279
                                · linarith only [h0, h1279, hlam]
                                · rcases p1269_3 (m.d 0 3) (by simp) with h1281 | h1281
                                  · linarith only [h1, h1281, hlam]
                                  · rcases p1269_3 (m.d 0 4) (by simp) with h1283 | h1283
                                    · linarith only [h1283, h2, hlam]
                                    · linarith only [h1062, h1283, hlam]
                              · linarith only [h1, h1278, hlam]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1264, h2, hc45, hlam, hphi, ht0b, ht5b, p1269_1, u0elo0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              rcases p1269_3 (m.d 0 1) (by simp) with h1288 | h1288
                              · rcases p1269_3 (m.d 0 2) (by simp) with h1289 | h1289
                                · linarith only [h0, h1289, hlam]
                                · rcases p1269_3 (m.d 0 3) (by simp) with h1291 | h1291
                                  · linarith only [h1, h1291, hlam]
                                  · rcases p1269_3 (m.d 0 4) (by simp) with h1293 | h1293
                                    · linarith only [h1293, h2, hlam]
                                    · linarith only [h1255, h1293, hlam]
                              · linarith only [h1288, h3, hlam]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h4, hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h790, hlam, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h981, hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1, hlam, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1198, hc02, hc35, hlam, hphi, ht23, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1062, hlam, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1198, hlam, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h2, hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, h790, hc12, hlam, hphi, p1269_1, u2elo3]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, h4, h790, hc12, hlam, hphi, p1269_1, u2elo3]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, h1198, h4, h790, hc12, hlam, hphi, p1269_1, u2elo3]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h3, hlam, p1269_0]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, h981, hc12, hlam, hphi, p1269_1, u2elo4]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h0, h4, h981, hc12, hlam, hphi, p1269_1, u2elo4]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [h1255, hlam, p1269_1]
                            · have p1269_0 := h1269c.1
                              have p1269_1 := h1269c.2.1
                              have p1269_2 := h1269c.2.2.1
                              have p1269_3 := h1269c.2.2.2
                              linarith only [hlam, p1269_0]
                          · linarith only [h1264, h1265, h1268, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1264, h1267, h2, h790, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1255, h1256, h1260, h1264, h790, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1320 | h1320
            · linarith only [h0, h1320, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1322 | h1322
              · linarith only [h0, h1322, h790, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1324 | h1324
                · linarith only [h1, h1062, h1324, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1326 | h1326
                  · linarith only [h1, h1198, h1326, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1328 | h1328
                    · linarith only [h1255, h1328, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1330 | h1330
                      · linarith only [h1062, h1330, h4, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1332 | h1332
                        · linarith only [h0, h1255, h1332, h790, hc12, hlam, hphi, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1334 | h1334
                          · linarith only [h0, h1332, h1334, h790, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1330, h1334, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1337 | h1337
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1338 | h1338
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1339 | h1339
      · linarith only [h0, h1339, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1341 | h1341
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1342 | h1342
          · linarith only [h1, h1342, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1344 | h1344
            · linarith only [h1344, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1348 | h1348
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1349 | h1349
                    · linarith only [h0, h1342, h1346, h1349, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1346, h1349, h3, hc23, hc35, hlam, hphi]
                  · linarith only [h1337, h1339, h1341, h1348, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h1338, h1339, h1347, hc12, hlam, hphi, u2elo4]
              · linarith only [h1337, h1339, h1346, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1355 | h1355
          · linarith only [h1, h1355, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1357 | h1357
            · linarith only [h0, h1338, h1339, h1357, h3, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1359 | h1359
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1360 | h1360
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1361 | h1361
                  · linarith only [h1, h1341, h1361, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1363 | h1363
                    · linarith only [h0, h1, h1355, h1359, h1363, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1359, h1363, h3, hc23, hc35, hlam, hphi]
                · linarith only [h1338, h1339, h1359, h1360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1337, h1339, h1359, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1368 | h1368
      · linarith only [h0, h1338, h1368, h3, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1370 | h1370
        · linarith only [h1337, h1338, h1370, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1372 | h1372
          · linarith only [h0, h1337, h1338, h1372, h3, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
            · linarith only [h1374, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1376 | h1376
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1377 | h1377
                · linarith only [h0, h1338, h1377, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1379 | h1379
                  · linarith only [h0, h1338, h1370, h1376, h1379, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1381 | h1381
                    · linarith only [h1, h1372, h1381, h3, hlam]
                    · linarith only [h1376, h1377, h1381, h2, h3, hc23, hc35, hlam, hphi]
              · linarith only [h1337, h1338, h1376, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1385 | h1385
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1386 | h1386
      · linarith only [h1, h1337, h1386, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1388 | h1388
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1389 | h1389
          · linarith only [h1, h1389, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1391 | h1391
            · linarith only [h1, h1337, h1385, h1391, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1393 | h1393
              · linarith only [h0, h1337, h1393, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1395 | h1395
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1397 | h1397
                    · linarith only [h1, h1386, h1389, h1397, h3, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
                      · linarith only [h1391, h1399, h2, h3, hlam]
                      · linarith only [h0, h1395, h1399, h3, hc24, hc45, hlam, hphi]
                  · linarith only [h1388, h1393, h1395, h1396, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1337, h1385, h1395, hc12, hlam, hphi, u2elo2]
        · linarith only [h1337, h1385, h1388, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1405 | h1405
      · linarith only [h0, h1337, h1405, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1407 | h1407
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1408 | h1408
          · linarith only [h1, h1408, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1410 | h1410
            · linarith only [h1, h1407, h1410, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
              · linarith only [h1337, h1412, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                · linarith only [h0, h1385, h1414, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1416 | h1416
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1417 | h1417
                    · linarith only [h1, h1408, h1417, h3, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1419 | h1419
                      · linarith only [h1410, h1419, h2, h3, hlam]
                      · linarith only [h1, h1416, h1419, h3, hc34, hc45, hlam, hphi]
                  · linarith only [h1407, h1408, h1416, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1423 | h1423
          · linarith only [h1, h1423, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1425 | h1425
            · linarith only [h1425, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
              · linarith only [h0, h1337, h1427, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                · linarith only [h0, h1385, h1429, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                  · linarith only [h1, h1407, h1431, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1433 | h1433
                    · linarith only [h0, h1, h1407, h1423, h1433, h3, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1435 | h1435
                      · linarith only [h1407, h1425, h1435, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1437 | h1437
                        · linarith only [h1, h1407, h1427, h1437, hc12, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1439 | h1439
                          · linarith only [h1435, h1439, h3, hc01, hlam, hphi, ht12, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1441 | h1441
                            · linarith only [h0, h1385, h1439, h1441, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1337, h1437, h1441, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1444 | h1444
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1445 | h1445
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1446 | h1446
      · linarith only [h0, h1446, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1448 | h1448
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1449 | h1449
          · linarith only [h1, h1449, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1451 | h1451
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1452 | h1452
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1453 | h1453
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1454 | h1454
                  · linarith only [h1446, h1454, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1453, h1454, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1445, h1446, h1453, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1445, h1446, h1451, h1452, h2, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1459 | h1459
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1460 | h1460
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1461 | h1461
                  · linarith only [h0, h1446, h1461, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1460, h1461, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1445, h1460, hc12, hlam, hphi, u2elo0]
              · linarith only [h0, h1446, h1448, h1459, h2, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
          · linarith only [h1444, h1445, h1448, h1466, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
            · linarith only [h1445, h1448, h1468, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1471 | h1471
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1472 | h1472
                  · linarith only [h0, h1446, h1472, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1471, h1472, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1445, h1471, hc12, hlam, hphi, u2elo0]
              · linarith only [h1444, h1470, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1477 | h1477
      · linarith only [h0, h1445, h1477, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1479 | h1479
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1480 | h1480
          · linarith only [h1, h1480, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1482 | h1482
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1483 | h1483
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1484 | h1484
                · linarith only [h1445, h1484, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1486 | h1486
                  · linarith only [h1, h1477, h1484, h1486, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1486, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1445, h1479, h1483, h2, hc12, hlam, hphi, u2elo2]
            · linarith only [h1445, h1479, h1482, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1491 | h1491
          · linarith only [h1, h1491, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1494 | h1494
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1495 | h1495
                · linarith only [h0, h1445, h1495, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1497 | h1497
                  · linarith only [h0, h1477, h1497, h2, hlam]
                  · linarith only [h1, h1495, h1497, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1493, h1494, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1501 | h1501
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1502 | h1502
                · linarith only [h0, h1445, h1502, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1504 | h1504
                  · linarith only [h0, h1477, h1504, h2, hlam]
                  · linarith only [h1, h1502, h1504, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1444, h1501, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1508 | h1508
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1509 | h1509
      · linarith only [h0, h1509, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1511 | h1511
        · linarith only [h0, h1444, h1511, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1513 | h1513
          · linarith only [h0, h1508, h1513, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1515 | h1515
            · linarith only [h0, h1444, h1508, h1515, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1517 | h1517
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1518 | h1518
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1519 | h1519
                  · linarith only [h0, h1509, h1519, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1518, h1519, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1444, h1508, h1509, h1517, h1518, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1523 | h1523
                · linarith only [h0, h1517, h1523, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1508, h1509, h1523, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1526 | h1526
      · linarith only [h0, h1508, h1526, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1528 | h1528
        · linarith only [h1, h1444, h1508, h1528, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1530 | h1530
          · linarith only [h1, h1530, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1532 | h1532
            · linarith only [h1, h1444, h1532, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1534 | h1534
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
                · linarith only [h0, h1508, h1535, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                  · linarith only [h0, h1444, h1526, h1534, h1537, hlam]
                  · linarith only [h1, h1535, h1537, h2, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                · linarith only [h0, h1534, h1540, h2, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1542 | h1542
                  · linarith only [h1, h1534, h1540, h1542, h2, hc24, hc45, hlam, hphi]
                  · linarith only [h1, h1540, h1542, h2, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1545 | h1545
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1546 | h1546
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1547 | h1547
      · linarith only [h0, h1, h1547, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1549 | h1549
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1550 | h1550
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1551 | h1551
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1552 | h1552
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1553 | h1553
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1547, h1549, h1554, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1, h1554, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                  · linarith only [h0, h1, h1547, h1557, hlam]
                  · linarith only [h0, h1, h1557, hc12, hlam, hphi, u2elo2]
              · linarith only [h0, h1, h1550, h1552, hlam]
            · linarith only [h0, h1, h1549, h1551, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1562 | h1562
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1563 | h1563
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1564 | h1564
                · linarith only [h1549, h1550, h1564, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1566 | h1566
                  · linarith only [h0, h1547, h1566, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1566, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1546, h1563, hlam]
            · linarith only [h0, h1, h1549, h1562, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1571 | h1571
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1572 | h1572
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1573 | h1573
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1574 | h1574
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1575 | h1575
                  · linarith only [h0, h1547, h1575, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1575, hc12, hlam, hphi, u2elo2]
                · linarith only [h1549, h1571, h1574, hlam]
              · linarith only [h1, h1545, h1549, h1571, h1573, hlam]
            · linarith only [h1, h1545, h1572, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1581 | h1581
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1583 | h1583
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
                  · linarith only [h0, h1547, h1584, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1584, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                  · linarith only [h0, h1, h1547, h1587, hlam]
                  · linarith only [h0, h1, h1587, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1546, h1582, hlam]
            · linarith only [h1, h1545, h1581, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1592 | h1592
      · linarith only [h0, h1, h1592, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1594 | h1594
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1595 | h1595
          · linarith only [h0, h1546, h1595, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1597 | h1597
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1598 | h1598
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1599 | h1599
                · linarith only [h0, h1546, h1594, h1599, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                  · linarith only [h0, h1592, h1601, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1601, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
                · linarith only [h0, h1, h1594, h1598, h1604, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h0, h1, h1598, h1606, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1606, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h1592, h1594, h1597, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1610 | h1610
          · linarith only [h1545, h1546, h1594, h1610, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1612 | h1612
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1613 | h1613
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1614 | h1614
                · linarith only [h1545, h1546, h1614, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1616 | h1616
                  · linarith only [h0, h1592, h1616, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1616, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1619 | h1619
                · linarith only [h1, h1545, h1613, h1619, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1621 | h1621
                  · linarith only [h0, h1, h1613, h1621, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1621, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1545, h1612, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1625 | h1625
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1626 | h1626
      · linarith only [h0, h1, h1626, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1628 | h1628
        · linarith only [h0, h1545, h1628, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1630 | h1630
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1631 | h1631
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1632 | h1632
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1633 | h1633
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1634 | h1634
                  · linarith only [h0, h1626, h1634, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1634, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1545, h1630, h1633, hlam]
              · linarith only [h0, h1, h1628, h1630, h1632, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1639 | h1639
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1640 | h1640
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
                  · linarith only [h0, h1, h1631, h1641, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1641, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h1628, h1630, h1631, h1640, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1, h1628, h1630, h1639, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1646 | h1646
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1647 | h1647
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1648 | h1648
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1649 | h1649
                  · linarith only [h0, h1626, h1646, h1649, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1649, hc12, hlam, hphi, u2elo2]
                · linarith only [h1545, h1625, h1648, hlam]
              · linarith only [h1, h1625, h1647, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1654 | h1654
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1655 | h1655
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
                  · linarith only [h0, h1, h1646, h1656, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1656, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h1625, h1646, h1655, hlam]
              · linarith only [h1, h1625, h1654, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1661 | h1661
      · linarith only [h0, h1, h1661, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1663 | h1663
        · linarith only [h0, h1545, h1663, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1665 | h1665
          · linarith only [h0, h1625, h1665, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1667 | h1667
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1668 | h1668
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1669 | h1669
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1670 | h1670
                  · linarith only [h0, h1661, h1670, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h1670, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1673 | h1673
                  · linarith only [h0, h1, h1661, h1667, h1673, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h1673, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1676 | h1676
                · linarith only [h1667, h1668, h1676, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1678 | h1678
                  · linarith only [h0, h1545, h1667, h1668, h1678, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1678, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1681 | h1681
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1682 | h1682
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1683 | h1683
                  · linarith only [h0, h1625, h1667, h1681, h1683, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1683, hc12, hlam, hphi, u2elo2]
                · linarith only [h1667, h1681, h1682, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1687 | h1687
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1688 | h1688
                  · linarith only [h0, h1, h1667, h1688, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h1688, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1691 | h1691
                  · linarith only [h0, h1, h1681, h1691, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1691, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x0 m hb0 hb2 hb4 h0 h1
  · exact r1l7_20_12_14_M_LI_L_0_L_I_x0_x1 m hb0 hb2 hb4 h0 h1

end R2N4
