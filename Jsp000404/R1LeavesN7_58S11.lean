import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h720 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h721 | h721
  · rcases m.htr 0 2 3 (by decide) (by decide) with h722 | h722
    · rcases m.htr 0 2 5 (by decide) (by decide) with h723 | h723
      · rcases m.htr 0 3 5 (by decide) (by decide) with h724 | h724
        · rcases m.htr 0 4 5 (by decide) (by decide) with h725 | h725
          · rcases m.htr 1 2 4 (by decide) (by decide) with h726 | h726
            · rcases m.htr 1 2 5 (by decide) (by decide) with h727 | h727
              · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
                · rcases m.htr 1 4 5 (by decide) (by decide) with h729 | h729
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h730 | h730
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h731 | h731
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h732 | h732
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h733 | h733
                          · rcases h0bigk with h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c | h734c
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, hlam, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p734_1, u3ehi0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h720, h727, h729, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p734_1, u3ehi0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, h720, h727, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, h721, h727, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h720, h727, h729, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h722, hlam, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, h720, h722, h727, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, h721, h722, h727, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h720, hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h720, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p734_1, u3ehi0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h0, h720, h721, h727, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p734_1, u2ehi4]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h721, hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h723, hlam, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h724, hlam, p734_0]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [h725, hlam, p734_1]
                            · have p734_0 := h734c.1
                              have p734_1 := h734c.2.1
                              have p734_2 := h734c.2.2.1
                              have p734_3 := h734c.2.2.2
                              linarith only [hlam, p734_0]
                          · linarith only [h0, h720, h725, h733, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h720, h729, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h722, h724, h730, h731, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h720, h728, h730, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h720, h725, h728, h729, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h765 | h765
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h766 | h766
                    · linarith only [h0, h722, h728, h766, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                      · linarith only [h0, h720, h726, h766, h768, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h771 | h771
                          · rcases h0bigk with h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c | h772c
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, hlam, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p772_1, u3ehi0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h724, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p772_1, u3ehi4]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p772_1, u3ehi0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h724, h725, h768, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h724, h768, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h720, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h722, hlam, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h722, h724, h725, h768, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h722, h724, h768, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h720, hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h720, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h720, h724, h768, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h0, h720, h724, h768, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p772_1, u2ehi2]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h721, hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h723, hlam, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h724, hlam, p772_0]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [h725, hlam, p772_1]
                            · have p772_0 := h772c.1
                              have p772_1 := h772c.2.1
                              have p772_2 := h772c.2.2.1
                              have p772_3 := h772c.2.2.2
                              linarith only [hlam, p772_0]
                          · linarith only [h0, h720, h725, h771, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h720, h765, h770, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h0, h720, h725, h726, h765, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h720, h726, h727, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h720, h723, h725, h726, hc24, hlam, hphi, u2ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h803 | h803
            · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
              · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
                · rcases m.htr 1 4 5 (by decide) (by decide) with h806 | h806
                  · linarith only [h0, h720, h725, h806, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h808 | h808
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h809 | h809
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h810 | h810
                        · linarith only [h720, h725, h803, h810, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h812 | h812
                          · linarith only [h720, h725, h803, h808, h812, hlam]
                          · rcases h0bigk with h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, hlam, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h720, h803, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h720, h803, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h720, h725, h803, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h721, h803, h806, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h722, hlam, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h720, h722, h803, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h720, h722, h725, h803, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h720, hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h725, hc45, hlam, hphi, ht34, p814_1, u3ehi0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h725, hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h721, hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h723, hlam, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h724, hlam, p814_0]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [h0, h721, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p814_1]
                            · have p814_0 := h814c.1
                              have p814_1 := h814c.2.1
                              have p814_2 := h814c.2.2.1
                              have p814_3 := h814c.2.2.2
                              linarith only [hlam, p814_0]
                      · linarith only [h0, h722, h724, h808, h809, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h720, h805, h808, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                  · linarith only [h0, h720, h725, h842, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                    · linarith only [h0, h722, h805, h844, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h846 | h846
                      · linarith only [h0, h720, h803, h844, h846, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h848 | h848
                        · linarith only [h720, h725, h803, h848, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h850 | h850
                          · linarith only [h720, h725, h803, h844, h850, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h805, h850, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h720, h803, h804, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h721, h723, h803, hc24, hlam, hphi, u2ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h855 | h855
          · rcases m.htr 1 2 4 (by decide) (by decide) with h856 | h856
            · rcases m.htr 1 2 5 (by decide) (by decide) with h857 | h857
              · rcases m.htr 1 3 4 (by decide) (by decide) with h858 | h858
                · rcases m.htr 1 4 5 (by decide) (by decide) with h859 | h859
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h860 | h860
                    · linarith only [h722, h724, h860, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h720, h858, h860, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h720, h855, h858, h859, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h864 | h864
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
                    · linarith only [h0, h722, h858, h865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h867 | h867
                      · linarith only [h724, h865, h867, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h869 | h869
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h870 | h870
                          · rcases h0bigk with h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c | h871c
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h722, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h722, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h720, h857, h864, h867, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h721, h857, h867, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h720, h857, h864, h867, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h722, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h720, h857, h864, h867, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h724, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h720, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p871_1, u3ehi0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h0, h720, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h721, hlam, p871_0]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h723, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h722, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p871_1, u2ehi2]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [h855, hlam, p871_1]
                            · have p871_0 := h871c.1
                              have p871_1 := h871c.2.1
                              have p871_2 := h871c.2.2.1
                              have p871_3 := h871c.2.2.2
                              linarith only [hlam, p871_0]
                          · linarith only [h0, h720, h856, h869, h870, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h720, h864, h869, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h720, h855, h856, h864, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h720, h856, h857, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h722, h856, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h902 | h902
            · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
              · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
                · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
                  · linarith only [h720, h855, h905, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h907 | h907
                    · linarith only [h722, h724, h907, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h721, h904, h905, h907, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
                  · linarith only [h720, h855, h910, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
                    · linarith only [h722, h904, h912, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
                      · linarith only [h0, h721, h724, h902, h910, h912, h914, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                        · linarith only [h720, h855, h902, h916, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
                          · linarith only [h720, h855, h902, h912, h918, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h904, h918, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h720, h902, h903, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h722, h902, hc24, hlam, hphi, u2ehi2]
      · linarith only [h722, h723, hc25, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h924 | h924
      · linarith only [h722, h924, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h721, h924, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h927 | h927
    · rcases m.htr 0 2 5 (by decide) (by decide) with h928 | h928
      · rcases m.htr 0 3 5 (by decide) (by decide) with h929 | h929
        · rcases m.htr 0 4 5 (by decide) (by decide) with h930 | h930
          · linarith only [h720, h721, h930, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h932 | h932
            · rcases m.htr 1 2 5 (by decide) (by decide) with h933 | h933
              · rcases m.htr 1 3 4 (by decide) (by decide) with h934 | h934
                · rcases m.htr 1 4 5 (by decide) (by decide) with h935 | h935
                  · linarith only [h720, h721, h930, h933, h935, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h720, h721, h932, h935, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h938 | h938
                  · linarith only [h720, h930, h938, hlam]
                  · linarith only [h720, h721, h932, h938, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · linarith only [h0, h720, h928, h932, h933, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h0, h927, h932, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h943 | h943
          · linarith only [h720, h721, h943, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
            · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
              · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                · rcases m.htr 1 4 5 (by decide) (by decide) with h948 | h948
                  · linarith only [h720, h721, h943, h946, h948, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h720, h721, h945, h948, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h951 | h951
                  · linarith only [h720, h943, h951, hlam]
                  · linarith only [h720, h721, h945, h951, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · linarith only [h0, h720, h945, h946, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h928, h945, hc24, hlam, hphi, u2ehi4]
      · linarith only [h927, h928, hc25, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h957 | h957
      · linarith only [h927, h957, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h959 | h959
        · rcases m.htr 0 4 5 (by decide) (by decide) with h960 | h960
          · linarith only [h0, h720, h957, h960, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h962 | h962
            · linarith only [h0, h720, h957, h962, hc25, hlam, hphi, u2ehi3]
            · linarith only [h0, h720, h962, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
          · linarith only [h0, h720, h927, h959, h965, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h967 | h967
            · linarith only [h0, h720, h927, h959, h967, hc35, hlam, hphi, ht23, u2ehi3]
            · linarith only [h0, h720, h967, hlam]

set_option maxHeartbeats 3626000 in
set_option maxHeartbeats 3626000 in
theorem r1l7_20_12_13_15_H_I_L_R_L_R_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h720 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h970 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h971 | h971
  · rcases m.htr 0 2 5 (by decide) (by decide) with h972 | h972
    · rcases m.htr 0 3 5 (by decide) (by decide) with h973 | h973
      · rcases m.htr 0 4 5 (by decide) (by decide) with h974 | h974
        · rcases m.htr 1 2 4 (by decide) (by decide) with h975 | h975
          · rcases m.htr 1 2 5 (by decide) (by decide) with h976 | h976
            · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
              · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
                · rcases m.htr 2 3 4 (by decide) (by decide) with h979 | h979
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h980 | h980
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h981 | h981
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h982 | h982
                        · rcases h0bigk with h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p983_1, u3ehi0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h720, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h720, h975, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p983_1, u3ehi0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, h720, h970, h976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, h970, h976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h970, h976, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h971, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, h720, h970, h971, h976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h0, h970, h971, h976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h970, h976, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h720, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h720, h975, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p983_1, u3ehi0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h720, h970, h975, h976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p983_1, u2ehi4]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h970, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h972, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h973, hlam, p983_0]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [h974, hlam, p983_1]
                          · have p983_0 := h983c.1
                            have p983_1 := h983c.2.1
                            have p983_2 := h983c.2.2.1
                            have p983_3 := h983c.2.2.2
                            linarith only [hlam, p983_0]
                        · linarith only [h0, h970, h978, h982, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h720, h970, h975, h978, h981, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h979, h980, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1012 | h1012
                    · linarith only [h1012, h977, h979, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1015 | h1015
                        · rcases h0bigk with h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c | h1016c
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h720, h975, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1016_1, u3ehi0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h720, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h720, h975, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1016_1, u3ehi0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, h1012, h720, h970, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, h1012, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1012, h970, h973, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h971, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, h1012, h720, h970, h971, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h0, h1012, h971, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1012, h970, h973, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h720, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1012, h720, h973, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h1012, h720, h973, h975, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1016_1, u2ehi2]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h970, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h972, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h973, hlam, p1016_0]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [h974, hlam, p1016_1]
                          · have p1016_0 := h1016c.1
                            have p1016_1 := h1016c.2.1
                            have p1016_2 := h1016c.2.2.1
                            have p1016_3 := h1016c.2.2.2
                            linarith only [hlam, p1016_0]
                        · linarith only [h1014, h1015, h975, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1014, h970, h978, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h720, h970, h973, h978, hc45, hlam, hphi, ht34, u3ehi4]
              · linarith only [h720, h970, h976, h977, hc34, hlam, hphi, ht23, u2ehi4]
            · linarith only [h0, h971, h976, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h971, h975, hc24, hlam, hphi, u2ehi2]
        · linarith only [h720, h970, h974, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1049 | h1049
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1050 | h1050
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1051 | h1051
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1052 | h1052
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
                  · linarith only [h1054, h971, h973, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1056 | h1056
                    · linarith only [h1052, h1054, h1056, h973, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1058 | h1058
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1059 | h1059
                        · rcases h0bigk with h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [hlam, p1060_0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h0, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h971, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h720, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1050, h720, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [hlam, p1060_0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h0, h971, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h0, h1051, h1056, h720, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h0, h1051, h1056, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1051, h1056, h970, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h971, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [hlam, p1060_0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1051, h1056, h720, h970, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h973, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1051, h1056, h970, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1050, h720, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1050, h720, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1060_1, u3ehi0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [hlam, p1060_0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1050, h1051, h1056, h720, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h970, hlam, p1060_0]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h972, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h971, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1060_1, u2ehi2]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [h1049, hlam, p1060_1]
                          · have p1060_0 := h1060c.1
                            have p1060_1 := h1060c.2.1
                            have p1060_2 := h1060c.2.2.1
                            have p1060_3 := h1060c.2.2.2
                            linarith only [hlam, p1060_0]
                        · linarith only [h1050, h1053, h1054, h1059, h720, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1050, h1053, h1054, h1058, h720, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h1053, h720, h970, h972, hc45, hlam, hphi, ht23, ht34, u2ehi4]
              · linarith only [h1051, h1052, h720, h970, hc34, hlam, hphi, ht23, u2ehi4]
            · linarith only [h0, h1051, h971, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h1050, h970, h971, h973, hc24, hlam, hphi, u2ehi2]
        · linarith only [h1049, h720, h970, hlam]
    · linarith only [h971, h972, hc25, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1094 | h1094
    · linarith only [h1094, h971, hc23, hlam, hphi, u2ehi4]
    · linarith only [h0, h1094, h970, hlam]

end R2N4
