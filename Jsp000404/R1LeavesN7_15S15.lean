import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S13
import Jsp000404.R1LeavesN7_15S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10112 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10539 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 4 (by decide) (by decide) with h10764 | h10764
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10765 | h10765
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10766 | h10766
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10767 | h10767
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10768 | h10768
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10769 | h10769
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10770 | h10770
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10771 | h10771
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10772 | h10772
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10773 | h10773
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10774 | h10774
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10775 | h10775
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10776 | h10776
                          · rcases h0bigk with h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c | h10777c
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h0, hlam, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h6253, hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h7338, hlam, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h8081, hlam, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10539, h10767, h10773, h10775, hc01, hc12, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h8735, hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10112, hlam, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10539, hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h6253, hc01, hc13, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10767, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10767, h8735, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h0, h10539, h10767, h8735, hc01, hc12, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h0, h10112, h10767, h10773, hc01, hc12, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10764, hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10112, h10767, h10773, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h0, h10539, h10767, h10773, h10775, hc01, hc12, hlam, hphi, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10765, hlam, p10777_0]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [h10766, hlam, p10777_1]
                            · have p10777_0 := h10777c.1
                              have p10777_1 := h10777c.2.1
                              have p10777_2 := h10777c.2.2.1
                              have p10777_3 := h10777c.2.2.2
                              linarith only [hlam, p10777_0]
                          · rcases h0bigk with h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c | h10803c
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h0, hlam, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h6253, hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h7338, hlam, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h8081, hlam, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h8735, hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10112, hlam, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10539, hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h8735, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h8735, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h8735, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h10770, h7338, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h0, h10112, h10767, h10773, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10764, hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h0, h10112, h10539, h10767, h10773, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10767, h10770, h10772, h8081, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h0, h10539, h10767, h10773, h10775, hc01, hc12, hlam, hphi, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10765, hlam, p10803_0]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [h10766, hlam, p10803_1]
                            · have p10803_0 := h10803c.1
                              have p10803_1 := h10803c.2.1
                              have p10803_2 := h10803c.2.2.1
                              have p10803_3 := h10803c.2.2.2
                              linarith only [hlam, p10803_0]
                        · linarith only [h10112, h10766, h10775, hlam]
                      · linarith only [h10765, h10774, h8735, hlam]
                    · linarith only [h10764, h10773, h8735, hlam]
                  · linarith only [h10112, h10766, h10772, h7338, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h10765, h10771, h6253, h8735, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10764, h10767, h10770, h8735, hlam]
            · linarith only [h0, h10767, h10769, h8735, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10767, h10768, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10837 | h10837
          · linarith only [h0, h10112, h10767, h10837, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10839 | h10839
            · linarith only [h0, h10539, h10767, h10839, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10841 | h10841
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10842 | h10842
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10843 | h10843
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10844 | h10844
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10845 | h10845
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10846 | h10846
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10847 | h10847
                          · rcases h0bigk with h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c | h10848c
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h0, hlam, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h6253, hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h7338, hlam, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h8081, hlam, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h0, h10839, h10844, h10846, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h8735, hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10112, hlam, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10539, hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h6253, hc01, hc13, hlam, hphi, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h8735, hc02, hc23, hlam, hphi, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h7338, h8735, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h0, h10539, h8735, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h0, h10112, h10844, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10764, hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10112, h10844, h8081, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h0, h10539, h10844, h10846, hc01, hc23, hlam, hphi, ht12, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10765, hlam, p10848_0]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [h10766, hlam, p10848_1]
                            · have p10848_0 := h10848c.1
                              have p10848_1 := h10848c.2.1
                              have p10848_2 := h10848c.2.2.1
                              have p10848_3 := h10848c.2.2.2
                              linarith only [hlam, p10848_0]
                          · rcases h0bigk with h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c | h10874c
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h0, hlam, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h6253, hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h7338, hlam, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h8081, hlam, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h0, h10839, h10844, h10846, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h8735, hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10112, hlam, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10539, hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10767, h6253, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10767, h6253, hc02, hc23, hlam, hphi, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10766, h10767, h10847, h6253, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10767, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10837, h10844, h7338, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h0, h10837, h10844, h7338, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10764, hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h0, h10539, h10837, h10844, h7338, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10839, h10844, h10846, h8081, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h0, h10839, h10844, h10846, h8081, hc01, hc23, hlam, hphi, ht12, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10765, hlam, p10874_0]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [h10766, hlam, p10874_1]
                            · have p10874_0 := h10874c.1
                              have p10874_1 := h10874c.2.1
                              have p10874_2 := h10874c.2.2.1
                              have p10874_3 := h10874c.2.2.2
                              linarith only [hlam, p10874_0]
                        · linarith only [h10766, h10837, h10846, h7338, hlam]
                      · linarith only [h10765, h10767, h10845, h6253, hlam]
                    · linarith only [h0, h10764, h10767, h10844, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h10766, h10843, h7338, hlam]
                · linarith only [h10765, h10842, h6253, hlam]
              · linarith only [h10764, h10841, h6253, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10906 | h10906
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10907 | h10907
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10908 | h10908
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10909 | h10909
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10910 | h10910
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10911 | h10911
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10912 | h10912
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10913 | h10913
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10914 | h10914
                        · linarith only [h10766, h10907, h10914, h7338, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10112, h10909, h10911, h10914, hc01, hc13, hlam, hphi]
                      · linarith only [h10765, h10913, h8735, hlam]
                    · linarith only [h10764, h10912, h8735, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10919 | h10919
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10920 | h10920
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10921 | h10921
                        · linarith only [h10911, h10921, h7338, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10923 | h10923
                          · linarith only [h10764, h10911, h10923, h7338, h8735, hc01, hc23, hlam, hphi, ht12]
                          · rcases h0bigk with h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c | h10925c
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h0, hlam, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h6253, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h7338, hlam, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h8081, hlam, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10112, h10907, hc01, hc14, hlam, hphi, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h8735, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10112, hlam, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10539, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10906, h8735, hc01, hc12, hlam, hphi, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10906, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h0, h10112, h10906, h8735, hc01, hc12, hlam, hphi, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10906, h8735, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10911, h7338, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h0, h10112, h10907, h10911, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10764, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10766, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h0, h10539, h10906, h10920, hc01, hc12, hlam, hphi, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10765, hlam, p10925_0]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [h10539, h10906, h10920, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10925_1]
                            · have p10925_0 := h10925c.1
                              have p10925_1 := h10925c.2.1
                              have p10925_2 := h10925c.2.2.1
                              have p10925_3 := h10925c.2.2.2
                              linarith only [hlam, p10925_0]
                      · linarith only [h10765, h10920, h8735, hlam]
                    · linarith only [h0, h10764, h10911, h10919, h7338, h8735, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h10765, h10910, h6253, hlam]
              · linarith only [h10764, h10906, h10909, h6253, h8735, hc01, hc12, hlam, hphi]
            · linarith only [h0, h10906, h10908, h8735, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h10906, h10907, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10957 | h10957
          · linarith only [h0, h10112, h10906, h10957, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10959 | h10959
            · linarith only [h0, h10539, h10906, h10959, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10961 | h10961
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10962 | h10962
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10963 | h10963
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10964 | h10964
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10965 | h10965
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10966 | h10966
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10967 | h10967
                          · linarith only [h0, h10112, h10764, h10766, h10967, h6253, hc01, hc13, hlam, hphi]
                          · rcases h0bigk with h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c | h10969c
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h0, hlam, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h6253, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h7338, hlam, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h8081, hlam, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10112, h10766, h10963, hc01, hc14, hlam, hphi, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h8735, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10112, hlam, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10539, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10906, h6253, hc01, hc23, hlam, hphi, ht12, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10906, h6253, hc02, hc23, hlam, hphi, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10906, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h0, h10112, h10766, h10906, h6253, hc01, hc23, hlam, hphi, ht12, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h0, h10112, h10964, hc01, hc23, hlam, hphi, ht12, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10764, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10766, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h0, h10539, h10964, h10966, hc01, hc23, hlam, hphi, ht12, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10765, hlam, p10969_0]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [h10766, h10963, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p10969_1]
                            · have p10969_0 := h10969c.1
                              have p10969_1 := h10969c.2.1
                              have p10969_2 := h10969c.2.2.1
                              have p10969_3 := h10969c.2.2.2
                              linarith only [hlam, p10969_0]
                        · linarith only [h10957, h10963, h10966, hlam]
                      · linarith only [h10765, h10766, h10957, h10963, h10964, h10965, hlam]
                    · linarith only [h10764, h10906, h10964, h6253, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10998 | h10998
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10999 | h10999
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11000 | h11000
                        · linarith only [h0, h10957, h10963, h10998, h11000, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h10957, h11000, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h10765, h10999, h6253, h8735, hc01, hc13, hlam, hphi]
                    · linarith only [h10764, h10906, h10998, h6253, hlam]
                · linarith only [h10765, h10962, h6253, hlam]
              · linarith only [h10764, h10961, h6253, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11007 | h11007
      · linarith only [h10764, h10765, h11007, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11009 | h11009
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11010 | h11010
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11011 | h11011
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11012 | h11012
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11013 | h11013
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11014 | h11014
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11015 | h11015
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11016 | h11016
                      · linarith only [h10764, h10765, h11009, h11016, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h11009, h11013, h11016, h8735, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h10764, h11009, h11015, h6253, h8735, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11020 | h11020
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11021 | h11021
                      · linarith only [h10764, h10765, h11009, h11021, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h11009, h11013, h11021, h8735, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h10764, h11009, h11020, h6253, h8735, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11025 | h11025
                  · linarith only [h11007, h11012, h11013, h11025, h7338, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11027 | h11027
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11028 | h11028
                      · linarith only [h11009, h11013, h11028, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11030 | h11030
                        · linarith only [h11025, h11030, h7338, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11032 | h11032
                          · linarith only [h10764, h10765, h11025, h11032, h8081, hlam]
                          · rcases h0bigk with h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c | h11034c
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, hlam, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h6253, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h7338, hlam, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h8081, hlam, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10112, h11010, hc01, hc14, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h8735, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10112, hlam, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10539, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11013, h11032, h6253, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11013, h11032, h6253, hc02, hc45, hlam, hphi, ht23, ht34, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, h10112, h11013, h11032, h6253, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10765, hlam, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, h10112, h11027, h11028, hc01, hc25, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10764, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h11007, hlam, p11034_0]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10539, hc01, hc25, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h0, h10539, hc01, hc25, hlam, hphi, ht12, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10765, h11032, hc03, hc45, hlam, hphi, ht34, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [h10765, h11032, hc04, hc45, hlam, hphi, p11034_1]
                            · have p11034_0 := h11034c.1
                              have p11034_1 := h11034c.2.1
                              have p11034_2 := h11034c.2.2.1
                              have p11034_3 := h11034c.2.2.2
                              linarith only [hlam, p11034_0]
                    · linarith only [h10764, h11013, h11027, h6253, hc23, hc35, hlam, hphi]
              · linarith only [h10764, h11012, h6253, hlam]
            · linarith only [h0, h11009, h11011, h8735, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11009, h11010, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11064 | h11064
          · linarith only [h0, h10112, h11009, h11064, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11066 | h11066
            · linarith only [h0, h10539, h11009, h11066, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11068 | h11068
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11069 | h11069
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11070 | h11070
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11071 | h11071
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11072 | h11072
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11073 | h11073
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11074 | h11074
                          · linarith only [h0, h10112, h10764, h10765, h11007, h11069, h11074, hc01, hc13, hlam, hphi]
                          · rcases h0bigk with h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c | h11076c
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h0, hlam, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h6253, hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h7338, hlam, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h8081, hlam, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h0, h11066, h11071, h11073, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h8735, hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10112, hlam, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10539, hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10765, hc01, hc35, hlam, hphi, ht12, ht23, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10765, h11074, hc02, hc45, hlam, hphi, ht23, ht34, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10765, h11074, hc04, hc45, hlam, hphi, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10765, hlam, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h11009, h11068, h7338, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h0, h11009, h11068, h7338, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h10764, hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h11007, hlam, p11076_0]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h11009, h11068, h11070, h8081, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h0, h11009, h11068, h11070, h8081, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h11009, h11068, h11070, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [h0, h10112, h11009, h11068, h11070, h8081, hc01, hc23, hlam, hphi, ht12, p11076_1]
                            · have p11076_0 := h11076c.1
                              have p11076_1 := h11076c.2.1
                              have p11076_2 := h11076c.2.2.1
                              have p11076_3 := h11076c.2.2.2
                              linarith only [hlam, p11076_0]
                        · linarith only [h0, h10112, h11009, h11068, h11070, h11073, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h11009, h11069, h11072, hlam]
                    · linarith only [h10764, h11009, h11071, h6253, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11105 | h11105
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11106 | h11106
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11107 | h11107
                        · linarith only [h11070, h11107, h7338, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h11064, h11107, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h11009, h11069, h11106, hlam]
                    · linarith only [h10764, h10765, h11009, h11069, h11105, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11112 | h11112
                  · linarith only [h10112, h11007, h11068, h11069, h11112, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11114 | h11114
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11115 | h11115
                      · linarith only [h11069, h11115, h6253, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h11009, h11115, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h10764, h11009, h11114, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h10764, h11068, h6253, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h11120 | h11120
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11121 | h11121
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11122 | h11122
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11123 | h11123
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11124 | h11124
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11125 | h11125
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11126 | h11126
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11127 | h11127
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11128 | h11128
                    · linarith only [h10764, h11120, h11122, h11128, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h11122, h11125, h11128, h8735, hc01, hc12, hlam, hphi]
                  · linarith only [h10539, h11121, h11124, h11127, h7338, hc01, hc12, hlam, hphi]
                · linarith only [h10764, h11125, h11126, hc03, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11133 | h11133
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11134 | h11134
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11135 | h11135
                    · linarith only [h11122, h11125, h11135, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11137 | h11137
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11138 | h11138
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11139 | h11139
                          · rcases h0bigk with h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c | h11140c
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h0, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h6253, hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h7338, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h8081, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h10539, h11137, hc01, hc23, hlam, hphi, ht12, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h8735, hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h10112, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h10539, hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11125, h6253, hc01, hc34, hlam, hphi, ht12, ht23, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11125, h6253, hc02, hc34, hlam, hphi, ht23, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h10764, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11125, h6253, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h0, h10112, hc01, hc24, hlam, hphi, ht12, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h10764, hc03, hc34, hlam, hphi, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h0, h10539, h10764, hc01, hc34, hlam, hphi, ht12, ht23, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11125, h11133, h8081, hc01, hc34, hlam, hphi, ht12, ht23, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h0, h11125, h11133, h8081, hc01, hc34, hlam, hphi, ht12, ht23, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11120, hlam, p11140_0]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [h11121, hlam, p11140_1]
                            · have p11140_0 := h11140c.1
                              have p11140_1 := h11140c.2.1
                              have p11140_2 := h11140c.2.2.1
                              have p11140_3 := h11140c.2.2.2
                              linarith only [hlam, p11140_0]
                          · linarith only [h11125, h11139, h6253, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h10112, h11121, h11138, hlam]
                      · linarith only [h11120, h11137, h8735, hlam]
                  · linarith only [h10112, h11121, h11123, h11134, hlam]
                · linarith only [h11120, h11122, h11133, h8735, hlam]
            · linarith only [h0, h11122, h11124, h8735, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11122, h11123, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11173 | h11173
          · linarith only [h0, h10112, h11122, h11173, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11175 | h11175
            · linarith only [h0, h10539, h11122, h11175, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11177 | h11177
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11178 | h11178
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11179 | h11179
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11180 | h11180
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11181 | h11181
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11182 | h11182
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11183 | h11183
                          · rcases h0bigk with h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c | h11184c
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h0, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h6253, hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h7338, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h8081, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h0, h11175, h11180, h11182, hc01, hc23, hlam, hphi, ht12, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h8735, hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h10112, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h10539, hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h11122, h6253, hc01, hc23, hlam, hphi, ht12, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h11122, h6253, hc02, hc23, hlam, hphi, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h10764, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h10764, h11177, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h0, h10112, h11180, hc01, hc23, hlam, hphi, ht12, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h10764, h11177, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h0, h10539, h10764, h11177, hc01, hc13, hlam, hphi, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h0, h10539, hc01, hc25, hlam, hphi, ht12, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h11120, hlam, p11184_0]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [h11121, hlam, p11184_1]
                            · have p11184_0 := h11184c.1
                              have p11184_1 := h11184c.2.1
                              have p11184_2 := h11184c.2.2.1
                              have p11184_3 := h11184c.2.2.2
                              linarith only [hlam, p11184_0]
                          · linarith only [h10764, h11121, h11183, hlam]
                        · linarith only [h10764, h11120, h11121, h11173, h11182, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h10764, h11122, h11177, h11181, hc03, hc35, hlam, hphi]
                    · linarith only [h11122, h11177, h11180, hlam]
                  · linarith only [h10764, h11120, h11121, h11177, h11179, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h10764, h11120, h11177, h11178, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11216 | h11216
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11217 | h11217
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11218 | h11218
                    · linarith only [h0, h11175, h11177, h11216, h11218, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11122, h11218, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h10764, h11120, h11121, h11217, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11120, h11216, h6253, hlam]
      · linarith only [h10764, h11120, h11121, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h11224 | h11224
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11225 | h11225
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11226 | h11226
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11227 | h11227
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11228 | h11228
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11229 | h11229
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11230 | h11230
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11231 | h11231
                    · linarith only [h0, h10764, h11225, h11231, h8735, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11225, h11228, h11231, h8735, hc01, hc12, hlam, hphi]
                  · linarith only [h10539, h11224, h11227, h11230, h7338, hc01, hc12, hlam, hphi]
                · linarith only [h0, h10764, h11228, h11229, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11236 | h11236
                · linarith only [h0, h11120, h11228, h11236, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11238 | h11238
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11239 | h11239
                    · linarith only [h11228, h11239, h6253, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11241 | h11241
                      · linarith only [h11225, h11236, h11241, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11243 | h11243
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11244 | h11244
                          · rcases h0bigk with h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c | h11245c
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h6253, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h7338, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h8081, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11225, h8735, hc01, hc13, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h8735, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10112, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10539, hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11236, h11244, h6253, hc01, hc34, hlam, hphi, ht12, ht23, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11225, h11236, h11244, h8735, hc02, hc34, hlam, hphi, ht23, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10764, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11120, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h10112, hc01, hc24, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10764, hc03, hc34, hlam, hphi, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10764, h8081, hc01, hc34, hlam, hphi, ht12, ht23, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h10539, hc01, hc25, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h10539, hc01, hc25, hlam, hphi, ht12, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h0, h11120, h11244, h8735, hc01, hc34, hlam, hphi, ht12, ht23, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [h11224, hlam, p11245_1]
                            · have p11245_0 := h11245c.1
                              have p11245_1 := h11245c.2.1
                              have p11245_2 := h11245c.2.2.1
                              have p11245_3 := h11245c.2.2.2
                              linarith only [hlam, p11245_0]
                          · linarith only [h10112, h11224, h11226, h11228, h11244, h7338, hc01, hc12, hlam, hphi]
                        · linarith only [h10112, h11224, h11243, hlam]
                  · linarith only [h10112, h11224, h11238, h7338, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h10112, h11226, h11227, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11225, h11226, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11276 | h11276
          · linarith only [h0, h10112, h11225, h11276, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11278 | h11278
            · linarith only [h0, h10539, h11225, h11278, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11280 | h11280
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11281 | h11281
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11282 | h11282
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11283 | h11283
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11284 | h11284
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11285 | h11285
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11286 | h11286
                          · rcases h0bigk with h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c | h11287c
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h0, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h6253, hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h7338, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h8081, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h11120, h11280, h11286, h8735, hc01, hc13, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h8735, hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h10112, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h10539, hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h11120, h11280, h11286, hc01, hc13, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h11120, h11280, h11286, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h10764, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h11120, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h0, h10112, h11283, hc01, hc23, hlam, hphi, ht12, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h10764, h11280, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [hlam, p11287_0]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h0, h10764, h11120, h11280, h8735, hc01, hc13, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h0, h10539, h11283, h11285, hc01, hc23, hlam, hphi, ht12, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h0, h11120, h11280, h11286, h8735, hc01, hc13, hlam, hphi, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [h11224, hlam, p11287_1]
                            · have p11287_0 := h11287c.1
                              have p11287_1 := h11287c.2.1
                              have p11287_2 := h11287c.2.2.1
                              have p11287_3 := h11287c.2.2.2
                              linarith only [hlam, p11287_0]
                          · linarith only [h10764, h11224, h11286, hlam]
                        · linarith only [h10764, h11224, h11276, h11285, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h11225, h11281, h11284, hlam]
                    · linarith only [h0, h11120, h11225, h11281, h11283, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11224, h11282, h7338, hlam]
                · linarith only [h0, h10764, h11280, h11281, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11319 | h11319
                · linarith only [h0, h11120, h11280, h11319, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11321 | h11321
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11322 | h11322
                    · linarith only [h11280, h11322, h6253, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11225, h11322, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h11224, h11321, h7338, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h11326 | h11326
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11327 | h11327
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11328 | h11328
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11329 | h11329
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11330 | h11330
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11331 | h11331
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11332 | h11332
                    · linarith only [h0, h10764, h11326, h11332, h8735, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11329, h11332, h8735, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11335 | h11335
                    · linarith only [h0, h10764, h11326, h11335, h8735, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h11329, h11331, h11335, h8735, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h10764, h11329, h11330, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11339 | h11339
                · linarith only [h0, h11120, h11329, h11339, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11341 | h11341
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11342 | h11342
                    · linarith only [h11329, h11342, h6253, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11344 | h11344
                      · linarith only [h11326, h11339, h11344, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11346 | h11346
                        · linarith only [h0, h10764, h11224, h11327, h11346, h8735, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10112, h11341, h11346, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11349 | h11349
                    · linarith only [h0, h10764, h11326, h11339, h11349, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11351 | h11351
                      · linarith only [h0, h11120, h11326, h11329, h11341, h11351, h8735, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11353 | h11353
                        · linarith only [h11329, h11341, h11353, h6253, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11355 | h11355
                          · linarith only [h0, h11326, h11329, h11341, h11355, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h11326, h11329, h11355, h8735, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h11326, h11328, h8735, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h11326, h11327, h8735, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11360 | h11360
          · linarith only [h0, h10112, h11326, h11360, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11362 | h11362
            · linarith only [h0, h10539, h11326, h11362, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11364 | h11364
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11365 | h11365
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11366 | h11366
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11367 | h11367
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11368 | h11368
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11369 | h11369
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11370 | h11370
                          · linarith only [h0, h10764, h11224, h11364, h11370, h8735, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h10764, h11366, h11370, h8735, hc01, hc14, hlam, hphi]
                        · linarith only [h11360, h11366, h11369, hlam]
                      · linarith only [h11326, h11365, h11368, hlam]
                    · linarith only [h0, h11120, h11326, h11365, h11367, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11376 | h11376
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11377 | h11377
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11378 | h11378
                        · linarith only [h11366, h11378, h7338, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h11360, h11378, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h11326, h11365, h11377, hlam]
                    · linarith only [h0, h11120, h11326, h11364, h11365, h11376, h8735, hc01, hc14, hlam, hphi]
                · linarith only [h0, h10764, h11364, h11365, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11384 | h11384
                · linarith only [h0, h11120, h11364, h11384, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11386 | h11386
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11387 | h11387
                    · linarith only [h11364, h11387, h6253, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11326, h11387, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11390 | h11390
                    · linarith only [h0, h11326, h11364, h11390, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11326, h11390, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10112 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 5 (by decide) (by decide) with h10539 | h10539
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h10112 h10539
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h10112 h10539

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 4 (by decide) (by decide) with h10112 | h10112
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h10112
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735 h10112

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 3 (by decide) (by decide) with h8735 | h8735
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1 m hb0 hb1 hb3 hb4 hg0 hg6253 hg7338 hg8081 h8735

end R2N4
