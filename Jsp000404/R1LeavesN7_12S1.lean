import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h696 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h698 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
  · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
    · rcases m.htr 2 3 4 (by decide) (by decide) with h701 | h701
      · rcases m.htr 2 3 5 (by decide) (by decide) with h702 | h702
        · rcases m.htr 2 4 5 (by decide) (by decide) with h703 | h703
          · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
            · linarith only [h1, h698, h704, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases h1bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                rcases p706_3 (m.d 0 1) (by simp) with h708 | h708
                · rcases p706_3 (m.d 1 2) (by simp) with h709 | h709
                  · linarith only [h709, hlam, p706_0]
                  · rcases p706_3 (m.d 1 3) (by simp) with h711 | h711
                    · linarith only [h1, h711, hlam]
                    · linarith only [h711, h9, hlam]
                · linarith only [h708, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h698, h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                rcases p706_3 (m.d 0 1) (by simp) with h717 | h717
                · rcases p706_3 (m.d 1 2) (by simp) with h718 | h718
                  · linarith only [h0, h718, hlam]
                  · rcases p706_3 (m.d 1 3) (by simp) with h720 | h720
                    · linarith only [h1, h720, hlam]
                    · linarith only [h699, h720, hlam]
                · linarith only [h717, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h9, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h619, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h696, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h1, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                rcases p706_3 (m.d 0 1) (by simp) with h730 | h730
                · rcases p706_3 (m.d 1 2) (by simp) with h731 | h731
                  · linarith only [h731, h9, hlam]
                  · rcases p706_3 (m.d 1 3) (by simp) with h733 | h733
                    · rcases p706_3 (m.d 1 4) (by simp) with h734 | h734
                      · linarith only [h698, h734, hlam]
                      · linarith only [h619, h734, hlam]
                    · linarith only [h733, h9, hlam]
                · linarith only [h0, h730, hlam]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, h4, h700, h704, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, h4, h700, h704, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h2, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                rcases p706_3 (m.d 0 1) (by simp) with h743 | h743
                · rcases p706_3 (m.d 1 2) (by simp) with h744 | h744
                  · linarith only [h619, h744, hlam]
                  · rcases p706_3 (m.d 1 3) (by simp) with h746 | h746
                    · rcases p706_3 (m.d 1 4) (by simp) with h747 | h747
                      · rcases p706_3 (m.d 1 5) (by simp) with h748 | h748
                        · linarith only [h700, h748, hlam]
                        · linarith only [h696, h748, hlam]
                      · linarith only [h619, h747, hlam]
                    · linarith only [h746, h9, hlam]
                · linarith only [h0, h743, hlam]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h698, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h2, h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h3, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                rcases p706_3 (m.d 0 1) (by simp) with h758 | h758
                · rcases p706_3 (m.d 1 2) (by simp) with h759 | h759
                  · linarith only [h696, h759, hlam]
                  · rcases p706_3 (m.d 1 3) (by simp) with h761 | h761
                    · rcases p706_3 (m.d 1 4) (by simp) with h762 | h762
                      · rcases p706_3 (m.d 1 5) (by simp) with h763 | h763
                        · rcases h2bigk with h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c | h764c
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h4, h696, h701, h703, hlam, p706_1, p764_2]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h0, h696, h701, h703, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h0, h696, h703, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h0, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h0, hlam, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h9, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h619, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h696, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h4, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            rcases p764_3 (m.d 0 2) (by simp) with h776 | h776
                            · rcases p764_3 (m.d 1 2) (by simp) with h777 | h777
                              · linarith only [h777, hlam, p764_0]
                              · rcases p764_3 (m.d 2 3) (by simp) with h779 | h779
                                · rcases p764_3 (m.d 2 4) (by simp) with h780 | h780
                                  · linarith only [h701, h780, hlam]
                                  · linarith only [h619, h780, hlam]
                                · linarith only [h779, hlam, p764_0]
                            · linarith only [h0, h776, hlam]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h696, h703, hc12, hc23, hlam, hphi, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h0, h4, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h5, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            rcases p764_3 (m.d 0 2) (by simp) with h789 | h789
                            · rcases p764_3 (m.d 1 2) (by simp) with h790 | h790
                              · linarith only [h790, hlam, p764_0]
                              · rcases p764_3 (m.d 2 3) (by simp) with h792 | h792
                                · rcases p764_3 (m.d 2 4) (by simp) with h793 | h793
                                  · rcases p764_3 (m.d 2 5) (by simp) with h794 | h794
                                    · linarith only [h703, h794, hlam]
                                    · linarith only [h696, h794, hlam]
                                  · linarith only [h793, hlam, p764_0]
                                · linarith only [h792, h9, hlam]
                            · linarith only [h0, h789, hlam]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h701, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h696, hc12, hc24, hlam, hphi, p706_1, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h6, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            rcases p764_3 (m.d 0 2) (by simp) with h804 | h804
                            · rcases p764_3 (m.d 1 2) (by simp) with h805 | h805
                              · linarith only [h805, hlam, p764_0]
                              · rcases p764_3 (m.d 2 3) (by simp) with h807 | h807
                                · rcases p764_3 (m.d 2 4) (by simp) with h808 | h808
                                  · rcases p764_3 (m.d 2 5) (by simp) with h809 | h809
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
                                        linarith only [h0, h4, h7, h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h0, h4, h619, h7, h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        rcases p810_3 (m.d 0 4) (by simp) with h814 | h814
                                        · rcases p810_3 (m.d 1 4) (by simp) with h815 | h815
                                          · linarith only [h2, h815, hlam]
                                          · linarith only [h698, h815, hlam]
                                        · linarith only [h7, h814, hlam]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        rcases p810_3 (m.d 0 4) (by simp) with h819 | h819
                                        · rcases p810_3 (m.d 1 4) (by simp) with h820 | h820
                                          · linarith only [h2, h820, hlam]
                                          · linarith only [h700, h820, hlam]
                                        · linarith only [h819, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h2, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h619, hlam, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        rcases p810_3 (m.d 0 4) (by simp) with h827 | h827
                                        · rcases p810_3 (m.d 1 4) (by simp) with h828 | h828
                                          · rcases p810_3 (m.d 2 4) (by simp) with h829 | h829
                                            · rcases p810_3 (m.d 3 4) (by simp) with h830 | h830
                                              · linarith only [h698, h830, hlam]
                                              · rcases p810_3 (m.d 4 5) (by simp) with h832 | h832
                                                · linarith only [h700, h832, hlam]
                                                · linarith only [h704, h832, hlam]
                                            · linarith only [h701, h829, hlam]
                                          · linarith only [h698, h828, hlam]
                                        · linarith only [h7, h827, hlam]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h0, h4, h698, h704, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h5, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h0, h5, h700, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        rcases p810_3 (m.d 0 4) (by simp) with h842 | h842
                                        · rcases p810_3 (m.d 1 4) (by simp) with h843 | h843
                                          · linarith only [h619, h843, hlam]
                                          · linarith only [h698, h843, hlam]
                                        · linarith only [h7, h842, hlam]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h0, h4, h701, h704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h7, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h698, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h701, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h704, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h8, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h700, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h703, hlam, p810_0]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [h2, h700, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p810_1]
                                      · have p810_0 := h810c.1
                                        have p810_1 := h810c.2.1
                                        have p810_2 := h810c.2.2.1
                                        have p810_3 := h810c.2.2.2
                                        linarith only [hlam, p810_0]
                                    · linarith only [h809, hlam, p764_0]
                                  · linarith only [h619, h808, hlam]
                                · linarith only [h807, h9, hlam]
                            · linarith only [h0, h804, hlam]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h702, hlam, p764_0]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [h703, hlam, p764_1]
                          · have p764_0 := h764c.1
                            have p764_1 := h764c.2.1
                            have p764_2 := h764c.2.2.1
                            have p764_3 := h764c.2.2.2
                            linarith only [hlam, p764_0]
                        · linarith only [h696, h763, hlam]
                      · linarith only [h619, h762, hlam]
                    · linarith only [h761, h9, hlam]
                · linarith only [h0, h758, hlam]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h699, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h700, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
          · linarith only [h619, h700, h703, hlam]
        · linarith only [h699, h702, h9, hlam]
      · linarith only [h0, h4, h699, h7, h701, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h875 | h875
      · rcases m.htr 2 3 5 (by decide) (by decide) with h876 | h876
        · rcases m.htr 2 4 5 (by decide) (by decide) with h877 | h877
          · rcases m.htr 3 4 5 (by decide) (by decide) with h878 | h878
            · linarith only [h698, h700, h878, hlam]
            · rcases h1bigk with h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c | h880c
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, h4, h619, h700, h875, h877, hlam, p880_2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h699, hc01, hlam, hphi, ht0b, ht5b, p880_1, u5ehi3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, h4, h700, h875, h877, hlam, p880_2]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                rcases p880_3 (m.d 0 1) (by simp) with h885 | h885
                · rcases p880_3 (m.d 1 2) (by simp) with h886 | h886
                  · linarith only [h0, h886, hlam]
                  · rcases p880_3 (m.d 1 3) (by simp) with h888 | h888
                    · linarith only [h1, h888, hlam]
                    · linarith only [h699, h888, hlam]
                · linarith only [h885, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h9, hlam, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h619, hlam, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h696, hlam, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h1, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                rcases p880_3 (m.d 0 1) (by simp) with h898 | h898
                · rcases p880_3 (m.d 1 2) (by simp) with h899 | h899
                  · linarith only [h899, h9, hlam]
                  · rcases p880_3 (m.d 1 3) (by simp) with h901 | h901
                    · rcases p880_3 (m.d 1 4) (by simp) with h902 | h902
                      · linarith only [h698, h902, hlam]
                      · linarith only [h619, h902, hlam]
                    · linarith only [h9, h901, hlam]
                · linarith only [h0, h898, hlam]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                rcases p880_3 (m.d 0 1) (by simp) with h908 | h908
                · rcases p880_3 (m.d 1 2) (by simp) with h909 | h909
                  · linarith only [h9, h909, hlam]
                  · rcases p880_3 (m.d 1 3) (by simp) with h911 | h911
                    · rcases p880_3 (m.d 1 4) (by simp) with h912 | h912
                      · linarith only [h698, h912, hlam]
                      · rcases p880_3 (m.d 1 5) (by simp) with h914 | h914
                        · linarith only [h699, h914, hlam]
                        · linarith only [h700, h914, hlam]
                    · linarith only [h698, h911, hlam]
                · linarith only [h2, h908, hlam]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h1, h699, hc01, hlam, hphi, ht0b, ht5b, p880_1, u5ehi3]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h2, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, h4, h700, h875, h877, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h698, hlam, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h700, hlam, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h3, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, h4, h700, h875, h877, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h699, hlam, p880_0]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [h0, h4, h700, h875, h877, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p880_1]
              · have p880_0 := h880c.1
                have p880_1 := h880c.2.1
                have p880_2 := h880c.2.2.1
                have p880_3 := h880c.2.2.2
                linarith only [hlam, p880_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h930 | h930
            · linarith only [h0, h4, h619, h7, h877, h930, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h0, h4, h619, h7, h8, h877, hlam, p932_2]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h699, hc01, hlam, hphi, ht0b, ht5b, p932_1, u5ehi3]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h936 | h936
                · rcases p932_3 (m.d 1 2) (by simp) with h937 | h937
                  · linarith only [h0, h937, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h939 | h939
                    · linarith only [h1, h939, hlam]
                    · linarith only [h698, h939, hlam]
                · linarith only [h936, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h943 | h943
                · rcases p932_3 (m.d 1 2) (by simp) with h944 | h944
                  · linarith only [h0, h944, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h946 | h946
                    · linarith only [h1, h946, hlam]
                    · linarith only [h699, h946, hlam]
                · linarith only [h943, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h0, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h9, hlam, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h619, hlam, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h696, hlam, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h1, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h956 | h956
                · rcases p932_3 (m.d 1 2) (by simp) with h957 | h957
                  · linarith only [h9, h957, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h959 | h959
                    · rcases p932_3 (m.d 1 4) (by simp) with h960 | h960
                      · linarith only [h698, h960, hlam]
                      · linarith only [h619, h960, hlam]
                    · linarith only [h9, h959, hlam]
                · linarith only [h0, h956, hlam]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h966 | h966
                · rcases p932_3 (m.d 1 2) (by simp) with h967 | h967
                  · linarith only [h9, h967, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h969 | h969
                    · rcases p932_3 (m.d 1 4) (by simp) with h970 | h970
                      · linarith only [h698, h970, hlam]
                      · rcases p932_3 (m.d 1 5) (by simp) with h972 | h972
                        · linarith only [h699, h972, hlam]
                        · linarith only [h700, h972, hlam]
                    · linarith only [h698, h969, hlam]
                · linarith only [h2, h966, hlam]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht5b, p932_1, u5ehi1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h2, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h0, h4, h619, h7, h8, h877, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h698, hlam, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h700, hlam, p932_1]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h3, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h984 | h984
                · rcases p932_3 (m.d 1 2) (by simp) with h985 | h985
                  · linarith only [h696, h985, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h987 | h987
                    · rcases p932_3 (m.d 1 4) (by simp) with h988 | h988
                      · linarith only [h700, h988, hlam]
                      · linarith only [h619, h988, hlam]
                    · linarith only [h9, h987, hlam]
                · linarith only [h0, h984, hlam]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [h699, hlam, p932_0]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                rcases p932_3 (m.d 0 1) (by simp) with h994 | h994
                · rcases p932_3 (m.d 1 2) (by simp) with h995 | h995
                  · linarith only [h696, h995, hlam]
                  · rcases p932_3 (m.d 1 3) (by simp) with h997 | h997
                    · rcases p932_3 (m.d 1 4) (by simp) with h998 | h998
                      · linarith only [h700, h998, hlam]
                      · rcases p932_3 (m.d 1 5) (by simp) with h1000 | h1000
                        · rcases h2bigk with h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h4, h619, h7, h8, h877, hlam, p1001_2]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h699, h9, hc01, hlam, hphi, ht0b, ht5b, p1001_1, u5ehi3]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            rcases p1001_3 (m.d 0 2) (by simp) with h1005 | h1005
                            · rcases p1001_3 (m.d 1 2) (by simp) with h1006 | h1006
                              · linarith only [h0, h1006, hlam]
                              · rcases p1001_3 (m.d 2 3) (by simp) with h1008 | h1008
                                · linarith only [h1008, h4, hlam]
                                · linarith only [h1008, h875, hlam]
                            · linarith only [h1005, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h619, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1001_1, p932_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, hlam, p1001_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h9, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h619, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h696, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h4, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            rcases p1001_3 (m.d 0 2) (by simp) with h1019 | h1019
                            · rcases p1001_3 (m.d 1 2) (by simp) with h1020 | h1020
                              · linarith only [h1020, hlam, p1001_0]
                              · rcases p1001_3 (m.d 2 3) (by simp) with h1022 | h1022
                                · rcases p1001_3 (m.d 2 4) (by simp) with h1023 | h1023
                                  · linarith only [h1023, h875, hlam]
                                  · linarith only [h1023, h619, hlam]
                                · linarith only [h1022, hlam, p1001_0]
                            · linarith only [h0, h1019, hlam]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h4, h619, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1001_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h4, h619, h696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1001_1, p932_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h5, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h4, h7, h8, h877, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1001_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h875, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h877, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h6, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            rcases p1001_3 (m.d 0 2) (by simp) with h1037 | h1037
                            · rcases p1001_3 (m.d 1 2) (by simp) with h1038 | h1038
                              · linarith only [h1038, hlam, p1001_0]
                              · rcases p1001_3 (m.d 2 3) (by simp) with h1040 | h1040
                                · rcases p1001_3 (m.d 2 4) (by simp) with h1041 | h1041
                                  · linarith only [h1041, h877, hlam]
                                  · linarith only [h1041, h619, hlam]
                                · linarith only [h1040, h9, hlam]
                            · linarith only [h0, h1037, hlam]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h876, hlam, p1001_0]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [h0, h6, h619, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1001_1]
                          · have p1001_0 := h1001c.1
                            have p1001_1 := h1001c.2.1
                            have p1001_2 := h1001c.2.2.1
                            have p1001_3 := h1001c.2.2.2
                            linarith only [hlam, p1001_0]
                        · linarith only [h1000, h700, hlam]
                    · linarith only [h698, h997, hlam]
                · linarith only [h2, h994, hlam]
              · have p932_0 := h932c.1
                have p932_1 := h932c.2.1
                have p932_2 := h932c.2.2.1
                have p932_3 := h932c.2.2.2
                linarith only [hlam, p932_0]
        · linarith only [h699, h876, h9, hlam]
      · linarith only [h2, h698, h699, h875, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1055 | h1055
    · linarith only [h1055, h698, h699, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1057 | h1057
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1058 | h1058
        · linarith only [h0, h1058, h4, h698, h699, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1060 | h1060
          · linarith only [h1055, h1057, h1058, h1060, h619, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1062 | h1062
            · linarith only [h1, h1060, h1062, h698, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, h1058, h1062, h4, h7, h8, h9, hlam, p1064_2]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                rcases p1064_3 (m.d 0 1) (by simp) with h1067 | h1067
                · rcases p1064_3 (m.d 1 2) (by simp) with h1068 | h1068
                  · linarith only [h0, h1068, hlam]
                  · rcases p1064_3 (m.d 1 3) (by simp) with h1070 | h1070
                    · linarith only [h1070, hlam, p1064_0]
                    · rcases p1064_3 (m.d 1 4) (by simp) with h1072 | h1072
                      · linarith only [h1072, h2, hlam]
                      · rcases p1064_3 (m.d 1 5) (by simp) with h1074 | h1074
                        · linarith only [h1074, h3, hlam]
                        · linarith only [h1074, h699, hlam]
                · linarith only [h1067, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                rcases p1064_3 (m.d 0 1) (by simp) with h1078 | h1078
                · rcases p1064_3 (m.d 1 2) (by simp) with h1079 | h1079
                  · linarith only [h0, h1079, hlam]
                  · rcases p1064_3 (m.d 1 3) (by simp) with h1081 | h1081
                    · linarith only [h1, h1081, hlam]
                    · linarith only [h1081, h698, hlam]
                · linarith only [h1078, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                rcases p1064_3 (m.d 0 1) (by simp) with h1085 | h1085
                · rcases p1064_3 (m.d 1 2) (by simp) with h1086 | h1086
                  · linarith only [h0, h1086, hlam]
                  · rcases p1064_3 (m.d 1 3) (by simp) with h1088 | h1088
                    · linarith only [h1, h1088, hlam]
                    · rcases p1064_3 (m.d 1 4) (by simp) with h1090 | h1090
                      · linarith only [h1090, h2, hlam]
                      · rcases p1064_3 (m.d 1 5) (by simp) with h1092 | h1092
                        · linarith only [h1092, hlam, p1064_0]
                        · rcases h2bigk with h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c | h1094c
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h1057, h1058, h1062, h4, h619, h7, h8, hlam, p1094_2]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            rcases p1094_3 (m.d 0 2) (by simp) with h1097 | h1097
                            · rcases p1094_3 (m.d 1 2) (by simp) with h1098 | h1098
                              · linarith only [h0, h1098, hlam]
                              · rcases p1094_3 (m.d 2 3) (by simp) with h1100 | h1100
                                · linarith only [h1100, hlam, p1094_0]
                                · rcases p1094_3 (m.d 2 4) (by simp) with h1102 | h1102
                                  · linarith only [h1102, h5, hlam]
                                  · rcases p1094_3 (m.d 2 5) (by simp) with h1104 | h1104
                                    · linarith only [h1104, h6, hlam]
                                    · linarith only [h1058, h1104, hlam]
                            · linarith only [h1097, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            rcases p1094_3 (m.d 0 2) (by simp) with h1108 | h1108
                            · rcases p1094_3 (m.d 1 2) (by simp) with h1109 | h1109
                              · linarith only [h0, h1109, hlam]
                              · rcases p1094_3 (m.d 2 3) (by simp) with h1111 | h1111
                                · linarith only [h1111, h4, hlam]
                                · linarith only [h1057, h1111, hlam]
                            · linarith only [h1108, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            rcases p1094_3 (m.d 0 2) (by simp) with h1115 | h1115
                            · rcases p1094_3 (m.d 1 2) (by simp) with h1116 | h1116
                              · linarith only [h0, h1116, hlam]
                              · rcases p1094_3 (m.d 2 3) (by simp) with h1118 | h1118
                                · linarith only [h1118, h4, hlam]
                                · rcases p1094_3 (m.d 2 4) (by simp) with h1120 | h1120
                                  · linarith only [h1120, h5, hlam]
                                  · rcases p1094_3 (m.d 2 5) (by simp) with h1122 | h1122
                                    · linarith only [h1122, hlam, p1094_0]
                                    · rcases h4bigk with h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        rcases p1124_3 (m.d 0 4) (by simp) with h1126 | h1126
                                        · rcases p1124_3 (m.d 1 4) (by simp) with h1127 | h1127
                                          · linarith only [h1127, h2, hlam]
                                          · rcases p1124_3 (m.d 2 4) (by simp) with h1129 | h1129
                                            · linarith only [h1129, h5, hlam]
                                            · linarith only [h1129, h619, hlam]
                                        · linarith only [h1126, h2, hlam]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        rcases p1124_3 (m.d 0 4) (by simp) with h1133 | h1133
                                        · rcases p1124_3 (m.d 1 4) (by simp) with h1134 | h1134
                                          · linarith only [h1134, h2, hlam]
                                          · rcases p1124_3 (m.d 2 4) (by simp) with h1136 | h1136
                                            · linarith only [h1136, h5, hlam]
                                            · rcases p1124_3 (m.d 3 4) (by simp) with h1138 | h1138
                                              · linarith only [h1138, h7, hlam]
                                              · rcases p1124_3 (m.d 4 5) (by simp) with h1140 | h1140
                                                · linarith only [h1140, h8, hlam]
                                                · linarith only [h1060, h1140, hlam]
                                        · linarith only [h1133, h5, hlam]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1058, h1062, h698, h8, h9, hlam, p1124_2]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h0, h1057, h1058, h1062, h4, h619, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h2, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h619, hlam, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1058, h1062, h698, h9, hc34, hc45, hlam, hphi, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1055, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h5, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h0, h1057, h1058, h1062, h4, h7, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h0, h1057, h1058, h1062, h4, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1060, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h7, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h698, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1057, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h1062, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h8, hlam, p1124_0]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        rcases p1124_3 (m.d 0 4) (by simp) with h1162 | h1162
                                        · rcases p1124_3 (m.d 1 4) (by simp) with h1163 | h1163
                                          · linarith only [h1163, hlam, p1124_0]
                                          · rcases p1124_3 (m.d 2 4) (by simp) with h1165 | h1165
                                            · linarith only [h1060, h1165, hlam]
                                            · linarith only [h1165, h619, hlam]
                                        · linarith only [h1162, h2, hlam]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [h0, h4, h619, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1124_1]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        rcases p1124_3 (m.d 0 4) (by simp) with h1170 | h1170
                                        · rcases p1124_3 (m.d 1 4) (by simp) with h1171 | h1171
                                          · linarith only [h1055, h1171, hlam]
                                          · linarith only [h1171, h698, hlam]
                                        · linarith only [h1170, h7, hlam]
                                      · have p1124_0 := h1124c.1
                                        have p1124_1 := h1124c.2.1
                                        have p1124_2 := h1124c.2.2.1
                                        have p1124_3 := h1124c.2.2.2
                                        linarith only [hlam, p1124_0]
                            · linarith only [h1115, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, hlam, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h9, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h619, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h696, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h4, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, h1058, h1062, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, h1058, h1062, h4, h619, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h1058, hlam, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h5, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, h1057, h1058, h1062, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h1057, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h1060, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h6, hlam, p1094_0]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            rcases p1094_3 (m.d 0 2) (by simp) with h1193 | h1193
                            · rcases p1094_3 (m.d 1 2) (by simp) with h1194 | h1194
                              · linarith only [h1194, hlam, p1094_0]
                              · rcases p1094_3 (m.d 2 3) (by simp) with h1196 | h1196
                                · linarith only [h1058, h1196, hlam]
                                · linarith only [h1196, h9, hlam]
                            · linarith only [h0, h1193, hlam]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [h0, h1058, h1062, h4, h619, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1094_1]
                          · have p1094_0 := h1094c.1
                            have p1094_1 := h1094c.2.1
                            have p1094_2 := h1094c.2.2.1
                            have p1094_3 := h1094c.2.2.2
                            linarith only [hlam, p1094_0]
                · linarith only [h1085, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h9, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h619, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h696, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h1, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, h1062, h4, h699, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, h1062, h4, h619, h699, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h699, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h2, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, h1062, h4, h698, h699, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h698, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h1055, hlam, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h3, hlam, p1064_0]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                rcases p1064_3 (m.d 0 1) (by simp) with h1220 | h1220
                · rcases p1064_3 (m.d 1 2) (by simp) with h1221 | h1221
                  · linarith only [h1221, h696, hlam]
                  · rcases p1064_3 (m.d 1 3) (by simp) with h1223 | h1223
                    · linarith only [h1223, h699, hlam]
                    · linarith only [h1223, h9, hlam]
                · linarith only [h0, h1220, hlam]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [h0, h1058, h1062, h4, h696, h698, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1064_1]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                rcases p1064_3 (m.d 0 1) (by simp) with h1228 | h1228
                · rcases p1064_3 (m.d 1 2) (by simp) with h1229 | h1229
                  · linarith only [h1229, h696, hlam]
                  · rcases p1064_3 (m.d 1 3) (by simp) with h1231 | h1231
                    · linarith only [h1231, h699, hlam]
                    · linarith only [h1231, h698, hlam]
                · linarith only [h1228, h2, hlam]
              · have p1064_0 := h1064c.1
                have p1064_1 := h1064c.2.1
                have p1064_2 := h1064c.2.2.1
                have p1064_3 := h1064c.2.2.2
                linarith only [hlam, p1064_0]
      · linarith only [h1, h1057, h698, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
