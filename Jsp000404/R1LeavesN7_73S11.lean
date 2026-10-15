import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_73S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_IR_L_R_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h692 | h692
  · linarith only [h0, h692, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h694 | h694
    · linarith only [h0, h694, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h696 | h696
      · linarith only [h0, h696, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h698 | h698
        · rcases m.htr 0 3 4 (by decide) (by decide) with h699 | h699
          · rcases m.htr 1 2 3 (by decide) (by decide) with h700 | h700
            · rcases m.htr 1 2 5 (by decide) (by decide) with h701 | h701
              · rcases m.htr 1 3 4 (by decide) (by decide) with h702 | h702
                · rcases m.htr 1 3 5 (by decide) (by decide) with h703 | h703
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h704 | h704
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h707 | h707
                          · linarith only [h698, h705, h707, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c | h709c
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h0, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h692, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h694, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, h702, h704, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, h704, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hc13, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h700, hlam, p709_1]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, h700, h704, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, h700, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hc14, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h700, h702, hlam, p709_1]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h702, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h696, h700, h702, hc12, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hc15, hlam, hphi, p709_1, u1ehi0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h701, hlam, p709_1]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h703, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [h704, hlam, p709_0]
                            · have p709_0 := h709c.1
                              have p709_1 := h709c.2.1
                              have p709_2 := h709c.2.2.1
                              have p709_3 := h709c.2.2.2
                              linarith only [hlam, p709_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h735 | h735
                          · linarith only [h700, h703, h705, h706, h735, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases h1bigk with h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h0, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h692, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h694, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h696, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hc12, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h702, h704, h706, h735, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h704, h705, h706, h735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hc12, hlam, hphi, p737_1, u1ehi4]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hc13, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h700, hlam, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h700, h704, h705, h706, h735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h696, h700, hc12, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hc14, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h700, h702, hlam, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h702, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h696, h700, h702, hc12, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hc15, hlam, hphi, p737_1, u1ehi0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h701, hlam, p737_1]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h703, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [h704, hlam, p737_0]
                            · have p737_0 := h737c.1
                              have p737_1 := h737c.2.1
                              have p737_2 := h737c.2.2.1
                              have p737_3 := h737c.2.2.2
                              linarith only [hlam, p737_0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h763 | h763
                        · linarith only [h699, h705, h763, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h765 | h765
                          · rcases h1bigk with h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c | h766c
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h0, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h692, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h694, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h696, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hc12, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h692, h699, h763, h765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p766_1]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hc12, hlam, hphi, p766_1, u1ehi3]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h696, hc12, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hc13, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h700, hlam, p766_1]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h694, h700, hc12, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h696, h700, hc12, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hc14, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h700, h702, hlam, p766_1]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h702, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h696, h700, h702, hc12, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hc15, hlam, hphi, p766_1, u1ehi0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h701, hlam, p766_1]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h703, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [h704, hlam, p766_0]
                            · have p766_0 := h766c.1
                              have p766_1 := h766c.2.1
                              have p766_2 := h766c.2.2.1
                              have p766_3 := h766c.2.2.2
                              linarith only [hlam, p766_0]
                          · rcases h1bigk with h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h0, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h692, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h694, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h696, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hc12, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h702, h704, h705, h765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h704, h705, h765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hc12, hlam, hphi, p792_1, u1ehi4]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hc13, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h700, hlam, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h700, h704, h705, h765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h696, h700, hc12, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hc14, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h700, h702, hlam, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h702, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h696, h700, h702, hc12, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hc15, hlam, hphi, p792_1, u1ehi0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h701, hlam, p792_1]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h703, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [h704, hlam, p792_0]
                            · have p792_0 := h792c.1
                              have p792_1 := h792c.2.1
                              have p792_2 := h792c.2.2.1
                              have p792_3 := h792c.2.2.2
                              linarith only [hlam, p792_0]
                    · linarith only [h694, h704, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                  · linarith only [h692, h703, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h692, h699, h702, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
              · linarith only [h0, h701, hc25, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h700, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h823 | h823
            · rcases m.htr 1 2 5 (by decide) (by decide) with h824 | h824
              · rcases m.htr 1 3 4 (by decide) (by decide) with h825 | h825
                · linarith only [h692, h699, h823, h825, hc12, hlam, hphi, u1ehi0]
                · linarith only [h692, h825, hc34, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h0, h824, hc25, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h698, h823, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h830 | h830
          · rcases m.htr 1 2 3 (by decide) (by decide) with h831 | h831
            · linarith only [h0, h698, h831, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h831, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h834 | h834
            · linarith only [h0, h698, h834, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h834, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_21_15_M_IR_L_R (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_M_IR_L_R_x0 m hb1 hb5 h0
  · exact r1l7_21_15_M_IR_L_R_x1 m hb1 hb5 h0

end R2N4
