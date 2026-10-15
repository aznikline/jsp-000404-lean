import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S82

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h39239 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h39240 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 2 3 5 (by decide) (by decide) with h39699 | h39699
  · rcases m.htr 2 4 5 (by decide) (by decide) with h39700 | h39700
    · rcases m.htr 3 4 5 (by decide) (by decide) with h39701 | h39701
      · rcases h1bigk with h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c | h39702c
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h0, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h33187, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h36828, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39707 | h39707
          · rcases p39702_3 (m.d 1 2) (by simp) with h39708 | h39708
            · rcases p39702_3 (m.d 1 3) (by simp) with h39709 | h39709
              · rcases p39702_3 (m.d 1 4) (by simp) with h39710 | h39710
                · rcases p39702_3 (m.d 1 5) (by simp) with h39711 | h39711
                  · linarith only [h39711, hlam, p39702_0]
                  · rcases h1emax with h39713 | h39713 | h39713 | h39713 | h39713
                    · linarith only [h39713, hc15, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · linarith only [h0, h39236, h39699, h39701, h39713, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · linarith only [h36828, h39236, h39237, h39699, h39701, h39713, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · linarith only [h36828, h39236, h39699, h39701, h39713, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · rcases h2bigk with h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c | h39718c
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h0, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39721 | h39721
                        · rcases p39718_3 (m.d 1 2) (by simp) with h39722 | h39722
                          · rcases p39718_3 (m.d 2 3) (by simp) with h39723 | h39723
                            · linarith only [h39723, hlam, p39718_0]
                            · rcases p39718_3 (m.d 2 4) (by simp) with h39725 | h39725
                              · linarith only [h39229, h39725, hlam]
                              · linarith only [h39240, h39725, hlam]
                          · linarith only [h39234, h39722, hlam]
                        · linarith only [h39721, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39730 | h39730
                        · rcases p39718_3 (m.d 1 2) (by simp) with h39731 | h39731
                          · rcases p39718_3 (m.d 2 3) (by simp) with h39732 | h39732
                            · linarith only [h39228, h39732, hlam]
                            · rcases p39718_3 (m.d 2 4) (by simp) with h39734 | h39734
                              · linarith only [h39734, hlam, p39718_0]
                              · rcases p39718_3 (m.d 2 5) (by simp) with h39736 | h39736
                                · linarith only [h39230, h39736, hlam]
                                · rcases h4bigk with h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c | h39738c
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h36828, hlam, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    rcases p39738_3 (m.d 0 4) (by simp) with h39741 | h39741
                                    · rcases p39738_3 (m.d 1 4) (by simp) with h39742 | h39742
                                      · rcases p39738_3 (m.d 2 4) (by simp) with h39743 | h39743
                                        · linarith only [h39229, h39743, hlam]
                                        · rcases p39738_3 (m.d 3 4) (by simp) with h39745 | h39745
                                          · linarith only [h39231, h39745, hlam]
                                          · linarith only [h39240, h39745, hlam]
                                      · linarith only [h39235, h39742, hlam]
                                    · linarith only [h39229, h39741, hlam]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39228, h39231, h39240, h39699, h39701, hc02, hc45, hlam, hphi, ht0b, ht5b, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    rcases p39738_3 (m.d 0 4) (by simp) with h39751 | h39751
                                    · rcases p39738_3 (m.d 1 4) (by simp) with h39752 | h39752
                                      · rcases p39738_3 (m.d 2 4) (by simp) with h39753 | h39753
                                        · linarith only [h39229, h39753, hlam]
                                        · linarith only [h39700, h39753, hlam]
                                      · linarith only [h39239, h39752, hlam]
                                    · linarith only [h39751, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h36828, h39236, h39699, h39701, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    rcases p39738_3 (m.d 0 4) (by simp) with h39760 | h39760
                                    · linarith only [h36828, h39760, hlam]
                                    · linarith only [h39229, h39760, hlam]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39234, h39237, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h36828, h39236, h39699, h39701, hlam, p39702_1, p39738_2]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39229, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39235, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39240, hlam, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39718_1, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39231, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39237, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39228, h39231, hlam, p39718_2, p39738_1]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    rcases p39738_3 (m.d 0 4) (by simp) with h39774 | h39774
                                    · rcases p39738_3 (m.d 1 4) (by simp) with h39775 | h39775
                                      · rcases p39738_3 (m.d 2 4) (by simp) with h39776 | h39776
                                        · linarith only [h39240, h39776, hlam]
                                        · linarith only [h39700, h39776, hlam]
                                      · linarith only [h39239, h39775, hlam]
                                    · linarith only [h39233, h39774, hlam]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39233, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39239, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39700, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [h39701, hlam, p39738_0]
                                  · have p39738_0 := h39738c.1
                                    have p39738_1 := h39738c.2.1
                                    have p39738_2 := h39738c.2.2.1
                                    have p39738_3 := h39738c.2.2.2
                                    linarith only [hlam, p39738_0]
                          · linarith only [h39235, h39731, hlam]
                        · linarith only [h39730, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39788 | h39788
                        · rcases p39718_3 (m.d 1 2) (by simp) with h39789 | h39789
                          · rcases p39718_3 (m.d 2 3) (by simp) with h39790 | h39790
                            · linarith only [h39228, h39790, hlam]
                            · linarith only [h39699, h39790, hlam]
                          · linarith only [h39236, h39789, hlam]
                        · linarith only [h39788, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39228, h39231, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39718_1]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39797 | h39797
                        · linarith only [h0, h39797, hlam]
                        · linarith only [h39228, h39797, hlam]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39800 | h39800
                        · linarith only [h0, h39800, hlam]
                        · linarith only [h39229, h39800, hlam]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h0, h39236, hlam, p39702_1, p39718_2]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39228, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39234, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39240, hlam, p39718_1]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39228, h39231, h39240, hc02, hc25, hlam, hphi, ht0b, ht5b, p39718_1]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39229, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39235, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h0, h39229, h39699, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p39718_1]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        rcases p39718_3 (m.d 0 2) (by simp) with h39813 | h39813
                        · rcases p39718_3 (m.d 1 2) (by simp) with h39814 | h39814
                          · rcases p39718_3 (m.d 2 3) (by simp) with h39815 | h39815
                            · linarith only [h39240, h39815, hlam]
                            · linarith only [h39699, h39815, hlam]
                          · linarith only [h39236, h39814, hlam]
                        · linarith only [h39230, h39813, hlam]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39230, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39236, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39699, hlam, p39718_0]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [h39700, hlam, p39718_1]
                      · have p39718_0 := h39718c.1
                        have p39718_1 := h39718c.2.1
                        have p39718_2 := h39718c.2.2.1
                        have p39718_3 := h39718c.2.2.2
                        linarith only [hlam, p39718_0]
                · linarith only [h39239, h39710, hlam]
              · linarith only [h39238, h39709, hlam]
            · linarith only [h39236, h39708, hlam]
          · linarith only [h39707, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39829 | h39829
          · linarith only [h39829, hlam, p39702_0]
          · rcases p39702_3 (m.d 1 2) (by simp) with h39831 | h39831
            · rcases p39702_3 (m.d 1 3) (by simp) with h39832 | h39832
              · linarith only [h39234, h39832, hlam]
              · linarith only [h33187, h39832, hlam]
            · linarith only [h39831, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p39702_1]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h36828, h39231, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39839 | h39839
          · linarith only [h0, h39839, hlam]
          · linarith only [h39227, h39839, hlam]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39842 | h39842
          · linarith only [h39842, hlam, p39702_0]
          · rcases p39702_3 (m.d 1 2) (by simp) with h39844 | h39844
            · rcases p39702_3 (m.d 1 3) (by simp) with h39845 | h39845
              · rcases p39702_3 (m.d 1 4) (by simp) with h39846 | h39846
                · linarith only [h39237, h39846, hlam]
                · linarith only [h36828, h39846, hlam]
              · linarith only [h39845, hlam, p39702_0]
            · linarith only [h0, h39844, hlam]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39234, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h36828, h39231, h39234, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39854 | h39854
          · linarith only [h33187, h39854, hlam]
          · linarith only [h39227, h39854, hlam]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h39857 | h39857
          · linarith only [h39857, hlam, p39702_0]
          · rcases p39702_3 (m.d 1 2) (by simp) with h39859 | h39859
            · rcases p39702_3 (m.d 1 3) (by simp) with h39860 | h39860
              · rcases p39702_3 (m.d 1 4) (by simp) with h39861 | h39861
                · rcases p39702_3 (m.d 1 5) (by simp) with h39862 | h39862
                  · linarith only [h39239, h39862, hlam]
                  · rcases h1emax with h39864 | h39864 | h39864 | h39864 | h39864
                    · rcases h2bigk with h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c | h39865c
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h0, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39868 | h39868
                        · rcases p39865_3 (m.d 1 2) (by simp) with h39869 | h39869
                          · rcases p39865_3 (m.d 2 3) (by simp) with h39870 | h39870
                            · linarith only [h39870, hlam, p39865_0]
                            · rcases p39865_3 (m.d 2 4) (by simp) with h39872 | h39872
                              · linarith only [h39229, h39872, hlam]
                              · linarith only [h39240, h39872, hlam]
                          · linarith only [h39234, h39869, hlam]
                        · linarith only [h39868, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39877 | h39877
                        · rcases p39865_3 (m.d 1 2) (by simp) with h39878 | h39878
                          · rcases p39865_3 (m.d 2 3) (by simp) with h39879 | h39879
                            · linarith only [h39228, h39879, hlam]
                            · rcases p39865_3 (m.d 2 4) (by simp) with h39881 | h39881
                              · linarith only [h39881, hlam, p39865_0]
                              · rcases p39865_3 (m.d 2 5) (by simp) with h39883 | h39883
                                · linarith only [h39230, h39883, hlam]
                                · rcases h4bigk with h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c | h39885c
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h36828, hlam, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    rcases p39885_3 (m.d 0 4) (by simp) with h39888 | h39888
                                    · rcases p39885_3 (m.d 1 4) (by simp) with h39889 | h39889
                                      · rcases p39885_3 (m.d 2 4) (by simp) with h39890 | h39890
                                        · linarith only [h39229, h39890, hlam]
                                        · rcases p39885_3 (m.d 3 4) (by simp) with h39892 | h39892
                                          · linarith only [h39231, h39892, hlam]
                                          · linarith only [h39240, h39892, hlam]
                                      · linarith only [h39235, h39889, hlam]
                                    · linarith only [h39229, h39888, hlam]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39228, h39231, h39240, h39699, h39701, hc02, hc45, hlam, hphi, ht0b, ht5b, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    rcases p39885_3 (m.d 0 4) (by simp) with h39898 | h39898
                                    · rcases p39885_3 (m.d 1 4) (by simp) with h39899 | h39899
                                      · rcases p39885_3 (m.d 2 4) (by simp) with h39900 | h39900
                                        · linarith only [h39229, h39900, hlam]
                                        · linarith only [h39700, h39900, hlam]
                                      · linarith only [h39239, h39899, hlam]
                                    · linarith only [h39898, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39231, h39240, h39699, h39701, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    rcases p39885_3 (m.d 0 4) (by simp) with h39907 | h39907
                                    · linarith only [h36828, h39907, hlam]
                                    · linarith only [h39229, h39907, hlam]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39237, h39240, h39699, h39701, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39227, h39236, h39699, h39701, hlam, p39702_1, p39885_2]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39229, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39235, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39240, hlam, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39865_1, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39231, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39237, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39228, h39231, hlam, p39865_2, p39885_1]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    rcases p39885_3 (m.d 0 4) (by simp) with h39921 | h39921
                                    · rcases p39885_3 (m.d 1 4) (by simp) with h39922 | h39922
                                      · rcases p39885_3 (m.d 2 4) (by simp) with h39923 | h39923
                                        · linarith only [h39240, h39923, hlam]
                                        · linarith only [h39700, h39923, hlam]
                                      · linarith only [h39239, h39922, hlam]
                                    · linarith only [h39233, h39921, hlam]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39233, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39239, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39700, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [h39701, hlam, p39885_0]
                                  · have p39885_0 := h39885c.1
                                    have p39885_1 := h39885c.2.1
                                    have p39885_2 := h39885c.2.2.1
                                    have p39885_3 := h39885c.2.2.2
                                    linarith only [hlam, p39885_0]
                          · linarith only [h39235, h39878, hlam]
                        · linarith only [h39877, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39935 | h39935
                        · rcases p39865_3 (m.d 1 2) (by simp) with h39936 | h39936
                          · rcases p39865_3 (m.d 2 3) (by simp) with h39937 | h39937
                            · linarith only [h39228, h39937, hlam]
                            · linarith only [h39699, h39937, hlam]
                          · linarith only [h39236, h39936, hlam]
                        · linarith only [h39935, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39228, h39231, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39865_1]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39944 | h39944
                        · linarith only [h0, h39944, hlam]
                        · linarith only [h39228, h39944, hlam]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39947 | h39947
                        · linarith only [h0, h39947, hlam]
                        · linarith only [h39229, h39947, hlam]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39227, h39235, h39236, hlam, p39702_1, p39865_2]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39228, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39234, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39240, hlam, p39865_1]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39228, h39231, h39240, hc02, hc25, hlam, hphi, ht0b, ht5b, p39865_1]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39229, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39235, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h0, h39228, h39231, h39240, h39699, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p39865_1]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        rcases p39865_3 (m.d 0 2) (by simp) with h39960 | h39960
                        · rcases p39865_3 (m.d 1 2) (by simp) with h39961 | h39961
                          · rcases p39865_3 (m.d 2 3) (by simp) with h39962 | h39962
                            · linarith only [h39240, h39962, hlam]
                            · linarith only [h39699, h39962, hlam]
                          · linarith only [h39236, h39961, hlam]
                        · linarith only [h39230, h39960, hlam]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39230, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39236, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39699, hlam, p39865_0]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [h39700, hlam, p39865_1]
                      · have p39865_0 := h39865c.1
                        have p39865_1 := h39865c.2.1
                        have p39865_2 := h39865c.2.2.1
                        have p39865_3 := h39865c.2.2.2
                        linarith only [hlam, p39865_0]
                    · linarith only [h39234, h39237, h39864, hc01, hlam, p39702_1]
                    · linarith only [h39227, h39236, h39237, h39699, h39701, h39864, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · linarith only [h39227, h39236, h39699, h39701, h39864, hc45, hlam, hphi, ht01, ht0b, ht5b, p39702_1]
                    · rcases h2bigk with h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c | h39975c
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h0, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h39978 | h39978
                        · rcases p39975_3 (m.d 1 2) (by simp) with h39979 | h39979
                          · rcases p39975_3 (m.d 2 3) (by simp) with h39980 | h39980
                            · linarith only [h39980, hlam, p39975_0]
                            · rcases p39975_3 (m.d 2 4) (by simp) with h39982 | h39982
                              · linarith only [h39229, h39982, hlam]
                              · linarith only [h39240, h39982, hlam]
                          · linarith only [h39234, h39979, hlam]
                        · linarith only [h39978, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h39987 | h39987
                        · rcases p39975_3 (m.d 1 2) (by simp) with h39988 | h39988
                          · rcases p39975_3 (m.d 2 3) (by simp) with h39989 | h39989
                            · linarith only [h39228, h39989, hlam]
                            · rcases p39975_3 (m.d 2 4) (by simp) with h39991 | h39991
                              · linarith only [h39991, hlam, p39975_0]
                              · rcases p39975_3 (m.d 2 5) (by simp) with h39993 | h39993
                                · linarith only [h39230, h39993, hlam]
                                · rcases h4bigk with h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c | h39995c
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h36828, hlam, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    rcases p39995_3 (m.d 0 4) (by simp) with h39998 | h39998
                                    · rcases p39995_3 (m.d 1 4) (by simp) with h39999 | h39999
                                      · rcases p39995_3 (m.d 2 4) (by simp) with h40000 | h40000
                                        · linarith only [h39229, h40000, hlam]
                                        · rcases p39995_3 (m.d 3 4) (by simp) with h40002 | h40002
                                          · linarith only [h39231, h40002, hlam]
                                          · linarith only [h39240, h40002, hlam]
                                      · linarith only [h39235, h39999, hlam]
                                    · linarith only [h39229, h39998, hlam]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39240, h39699, h39701, hc04, hc45, hlam, hphi, ht0b, ht5b, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    rcases p39995_3 (m.d 0 4) (by simp) with h40008 | h40008
                                    · rcases p39995_3 (m.d 1 4) (by simp) with h40009 | h40009
                                      · rcases p39995_3 (m.d 2 4) (by simp) with h40010 | h40010
                                        · linarith only [h39229, h40010, hlam]
                                        · linarith only [h39700, h40010, hlam]
                                      · linarith only [h39239, h40009, hlam]
                                    · linarith only [h40008, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39231, h39234, h39237, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    rcases p39995_3 (m.d 0 4) (by simp) with h40017 | h40017
                                    · linarith only [h36828, h40017, hlam]
                                    · linarith only [h39229, h40017, hlam]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39234, h39237, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39227, h39236, h39699, h39701, hlam, p39702_1, p39995_2]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39229, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39235, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39240, hlam, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39975_1, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39231, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39237, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39228, h39231, hlam, p39975_2, p39995_1]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    rcases p39995_3 (m.d 0 4) (by simp) with h40031 | h40031
                                    · rcases p39995_3 (m.d 1 4) (by simp) with h40032 | h40032
                                      · rcases p39995_3 (m.d 2 4) (by simp) with h40033 | h40033
                                        · linarith only [h39240, h40033, hlam]
                                        · linarith only [h39700, h40033, hlam]
                                      · linarith only [h39239, h40032, hlam]
                                    · linarith only [h39233, h40031, hlam]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39233, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39239, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39700, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [h39701, hlam, p39995_0]
                                  · have p39995_0 := h39995c.1
                                    have p39995_1 := h39995c.2.1
                                    have p39995_2 := h39995c.2.2.1
                                    have p39995_3 := h39995c.2.2.2
                                    linarith only [hlam, p39995_0]
                          · linarith only [h39235, h39988, hlam]
                        · linarith only [h39987, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h40045 | h40045
                        · rcases p39975_3 (m.d 1 2) (by simp) with h40046 | h40046
                          · rcases p39975_3 (m.d 2 3) (by simp) with h40047 | h40047
                            · linarith only [h39228, h40047, hlam]
                            · linarith only [h39699, h40047, hlam]
                          · linarith only [h39236, h40046, hlam]
                        · linarith only [h40045, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39228, h39231, h39240, h39699, h39701, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p39975_1]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h40054 | h40054
                        · linarith only [h0, h40054, hlam]
                        · linarith only [h39228, h40054, hlam]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h40057 | h40057
                        · linarith only [h0, h40057, hlam]
                        · linarith only [h39229, h40057, hlam]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39227, h39235, h39236, hlam, p39702_1, p39975_2]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39228, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39234, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39240, hlam, p39975_1]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39228, h39231, h39240, hc02, hc25, hlam, hphi, ht0b, ht5b, p39975_1]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39229, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39235, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39229, h39699, hc02, hc35, hlam, hphi, ht0b, ht5b, p39975_1]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        rcases p39975_3 (m.d 0 2) (by simp) with h40070 | h40070
                        · rcases p39975_3 (m.d 1 2) (by simp) with h40071 | h40071
                          · rcases p39975_3 (m.d 2 3) (by simp) with h40072 | h40072
                            · linarith only [h39240, h40072, hlam]
                            · linarith only [h39699, h40072, hlam]
                          · linarith only [h39236, h40071, hlam]
                        · linarith only [h39230, h40070, hlam]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39230, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39236, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39699, hlam, p39975_0]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [h39700, hlam, p39975_1]
                      · have p39975_0 := h39975c.1
                        have p39975_1 := h39975c.2.1
                        have p39975_2 := h39975c.2.2.1
                        have p39975_3 := h39975c.2.2.2
                        linarith only [hlam, p39975_0]
                · linarith only [h39861, hlam, p39702_0]
              · linarith only [h33187, h39860, hlam]
            · linarith only [h0, h39859, hlam]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39235, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39237, hlam, p39702_1]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          rcases p39702_3 (m.d 0 1) (by simp) with h40088 | h40088
          · linarith only [h36828, h40088, hlam]
          · linarith only [h39227, h40088, hlam]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39227, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39236, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39238, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [h39239, hlam, p39702_0]
        · have p39702_0 := h39702c.1
          have p39702_1 := h39702c.2.1
          have p39702_2 := h39702c.2.2.1
          have p39702_3 := h39702c.2.2.2
          linarith only [hlam, p39702_0]
      · linarith only [h39227, h39239, h39240, h39699, h39701, hc01, hc35, hlam, hphi, ht0b, ht5b]
    · linarith only [h36828, h39227, h39234, h39237, h39239, h39240, h39699, h39700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h40098 | h40098
    · rcases m.htr 3 4 5 (by decide) (by decide) with h40099 | h40099
      · rcases h1bigk with h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c | h40100c
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h0, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h33187, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h36828, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h36828, h39234, h39237, h39238, h39699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39227, h39238, h39699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h36828, h39227, h39238, h39699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          rcases p40100_3 (m.d 0 1) (by simp) with h40110 | h40110
          · linarith only [h0, h40110, hlam]
          · linarith only [h39227, h40110, hlam]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39227, h39238, h39699, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39234, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h36828, h39227, h39234, h39238, h39699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          rcases p40100_3 (m.d 0 1) (by simp) with h40117 | h40117
          · linarith only [h33187, h40117, hlam]
          · linarith only [h39227, h40117, hlam]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39227, h39238, h39699, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39235, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39237, hlam, p40100_1]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          rcases p40100_3 (m.d 0 1) (by simp) with h40124 | h40124
          · linarith only [h36828, h40124, hlam]
          · linarith only [h39227, h40124, hlam]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39227, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39236, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39238, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [h39239, hlam, p40100_0]
        · have p40100_0 := h40100c.1
          have p40100_1 := h40100c.2.1
          have p40100_2 := h40100c.2.2.1
          have p40100_3 := h40100c.2.2.2
          linarith only [hlam, p40100_0]
      · linarith only [h0, h39229, h39240, h40098, h40099, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h40133 | h40133
      · rcases h1bigk with h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c | h40134c
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h0, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h33187, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h36828, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h0, h39238, h39240, h40098, h40133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39227, h39238, h39240, h40098, h40133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h33187, hc01, hc12, hlam, hphi, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h36828, h39227, h39238, h39240, h40098, h40133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          rcases p40134_3 (m.d 0 1) (by simp) with h40144 | h40144
          · linarith only [h0, h40144, hlam]
          · linarith only [h39227, h40144, hlam]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39227, h39238, h39240, h40098, h40133, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39234, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h36828, h39227, h39234, h39238, h39240, h40098, h40133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          rcases p40134_3 (m.d 0 1) (by simp) with h40151 | h40151
          · linarith only [h33187, h40151, hlam]
          · linarith only [h39227, h40151, hlam]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39227, h39238, h39240, h40098, h40133, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39235, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39237, hlam, p40134_1]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          rcases p40134_3 (m.d 0 1) (by simp) with h40158 | h40158
          · linarith only [h36828, h40158, hlam]
          · linarith only [h39227, h40158, hlam]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39227, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39236, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39238, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [h39239, hlam, p40134_0]
        · have p40134_0 := h40134c.1
          have p40134_1 := h40134c.2.1
          have p40134_2 := h40134c.2.2.1
          have p40134_3 := h40134c.2.2.2
          linarith only [hlam, p40134_0]
      · linarith only [h0, h39227, h39239, h39240, h40133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h39239 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 2 3 4 (by decide) (by decide) with h39240 | h39240
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238 h39239 h39240
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238 h39239 h39240

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h39239 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h0, h36828, h39228, h39231, h39233, h39239, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 4 5 (by decide) (by decide) with h39239 | h39239
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238 h39239
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238 h39239

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h39238 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h33187, h39232, h39238, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 3 5 (by decide) (by decide) with h39238 | h39238
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237 h39238

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h39237 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h33187, h39231, h39237, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 3 4 (by decide) (by decide) with h39237 | h39237
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236 h39237

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h39236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h0, h39230, h39236, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 2 5 (by decide) (by decide) with h39236 | h39236
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235 h39236

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h39235 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h0, h39229, h39235, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 2 4 (by decide) (by decide) with h39235 | h39235
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234 h39235

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h39234 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h0, h39228, h39234, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 1 2 3 (by decide) (by decide) with h39234 | h39234
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233 h39234

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h39233 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h36828, h39227, h39233, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 4 5 (by decide) (by decide) with h39233 | h39233
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232 h39233

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h39232 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h33187, h39227, h39232, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 3 5 (by decide) (by decide) with h39232 | h39232
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231 h39232

end R2N4
