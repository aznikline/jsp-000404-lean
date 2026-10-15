import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S14
import Jsp000404.R1LeavesN7_6S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8478 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h8480 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases h0bigk with h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c | h8730c
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h0, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8733 | h8733
    · rcases p8730_3 (m.d 0 2) (by simp) with h8734 | h8734
      · rcases p8730_3 (m.d 0 3) (by simp) with h8735 | h8735
        · linarith only [h6793, h8735, hlam]
        · rcases p8730_3 (m.d 0 4) (by simp) with h8737 | h8737
          · linarith only [h6794, h8737, hlam]
          · linarith only [h6799, h8737, hlam]
      · linarith only [h6796, h8734, hlam]
    · linarith only [h6793, h8733, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8742 | h8742
    · rcases p8730_3 (m.d 0 2) (by simp) with h8743 | h8743
      · rcases p8730_3 (m.d 0 3) (by simp) with h8744 | h8744
        · linarith only [h6793, h8744, hlam]
        · rcases p8730_3 (m.d 0 4) (by simp) with h8746 | h8746
          · linarith only [h6794, h8746, hlam]
          · rcases p8730_3 (m.d 0 5) (by simp) with h8748 | h8748
            · linarith only [h6795, h8748, hlam]
            · linarith only [h7593, h8748, hlam]
      · linarith only [h6797, h8743, hlam]
    · linarith only [h6794, h8742, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8753 | h8753
    · rcases p8730_3 (m.d 0 2) (by simp) with h8754 | h8754
      · rcases p8730_3 (m.d 0 3) (by simp) with h8755 | h8755
        · linarith only [h6793, h8755, hlam]
        · rcases p8730_3 (m.d 0 4) (by simp) with h8757 | h8757
          · linarith only [h6794, h8757, hlam]
          · rcases p8730_3 (m.d 0 5) (by simp) with h8759 | h8759
            · linarith only [h6795, h8759, hlam]
            · rcases h0emin with h8761 | h8761 | h8761 | h8761 | h8761
              · rcases h2bigk with h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c | h8762c
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, hlam, p8762_1]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  rcases p8762_3 (m.d 0 2) (by simp) with h8765 | h8765
                  · rcases p8762_3 (m.d 1 2) (by simp) with h8766 | h8766
                    · rcases p8762_3 (m.d 2 3) (by simp) with h8767 | h8767
                      · linarith only [h8767, hlam, p8762_0]
                      · rcases p8762_3 (m.d 2 4) (by simp) with h8769 | h8769
                        · linarith only [h6797, h8769, hlam]
                        · linarith only [h8474, h8769, hlam]
                    · linarith only [h8467, h8766, hlam]
                  · linarith only [h8765, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  rcases p8762_3 (m.d 0 2) (by simp) with h8774 | h8774
                  · rcases p8762_3 (m.d 1 2) (by simp) with h8775 | h8775
                    · rcases p8762_3 (m.d 2 3) (by simp) with h8776 | h8776
                      · linarith only [h6796, h8776, hlam]
                      · rcases p8762_3 (m.d 2 4) (by simp) with h8778 | h8778
                        · linarith only [h8778, hlam, p8762_0]
                        · rcases p8762_3 (m.d 2 5) (by simp) with h8780 | h8780
                          · linarith only [h6798, h8780, hlam]
                          · linarith only [h8478, h8780, hlam]
                    · linarith only [h8468, h8775, hlam]
                  · linarith only [h8774, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  rcases p8762_3 (m.d 0 2) (by simp) with h8785 | h8785
                  · rcases p8762_3 (m.d 1 2) (by simp) with h8786 | h8786
                    · rcases p8762_3 (m.d 2 3) (by simp) with h8787 | h8787
                      · linarith only [h6796, h8787, hlam]
                      · rcases p8762_3 (m.d 2 4) (by simp) with h8789 | h8789
                        · linarith only [h6797, h8789, hlam]
                        · rcases p8762_3 (m.d 2 5) (by simp) with h8791 | h8791
                          · linarith only [h8791, hlam, p8762_0]
                          · rcases h4bigk with h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6799, h8467, h8470, h8480, hc23, hc45, hlam, hphi, ht34, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6799, h8474, h8480, hc23, hc45, hlam, hphi, ht34, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6799, hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h7593, hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6794, hlam, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h0, h6794, h8474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8470, hlam, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8472, hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6797, hlam, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8468, hlam, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8474, hlam, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8478, hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8480, hc04, hc45, hlam, hphi, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8468, h8474, h8480, hc23, hc45, hlam, hphi, ht34, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8474, h8480, hc23, hc45, hlam, hphi, ht34, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h8480, hlam, p8793_0]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              rcases p8793_3 (m.d 0 4) (by simp) with h8814 | h8814
                              · linarith only [h8814, hlam, p8793_0]
                              · rcases p8793_3 (m.d 1 4) (by simp) with h8816 | h8816
                                · linarith only [h8472, h8816, hlam]
                                · rcases p8793_3 (m.d 2 4) (by simp) with h8818 | h8818
                                  · linarith only [h8478, h8818, hlam]
                                  · rcases p8793_3 (m.d 3 4) (by simp) with h8820 | h8820
                                    · linarith only [h8480, h8820, hlam]
                                    · linarith only [h6799, h8820, hlam]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              rcases p8793_3 (m.d 0 4) (by simp) with h8823 | h8823
                              · linarith only [h7593, h8823, hlam]
                              · linarith only [h6794, h8823, hlam]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              rcases p8793_3 (m.d 0 4) (by simp) with h8826 | h8826
                              · linarith only [h7593, h8826, hlam]
                              · linarith only [h6797, h8826, hlam]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [h6793, h6799, h8467, hc23, hc45, hlam, hphi, ht34, p8793_1]
                            · have p8793_0 := h8793c.1
                              have p8793_1 := h8793c.2.1
                              have p8793_2 := h8793c.2.2.1
                              have p8793_3 := h8793c.2.2.2
                              linarith only [hlam, p8793_0]
                    · linarith only [h8469, h8786, hlam]
                  · linarith only [h8785, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h8761, hc12, hlam, ht01, p8762_1]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hlam, p8730_1, p8762_2]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h6794, h7593, h8468, hlam, p8730_1, p8762_2]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h6795, h8469, hlam, p8730_1, p8762_2]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h6796, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8467, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8474, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8476, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h6797, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8468, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h6794, h7593, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8762_1, u0elo0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8478, hlam, p8762_1]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h6798, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h8469, hlam, p8762_0]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h6795, h8469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8762_1, u0elo1]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p8730_1, p8762_1, u0elo1]
                · have p8762_0 := h8762c.1
                  have p8762_1 := h8762c.2.1
                  have p8762_2 := h8762c.2.2.1
                  have p8762_3 := h8762c.2.2.2
                  linarith only [hlam, p8762_0]
              · rcases h2bigk with h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c | h8853c
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, hlam, p8853_1]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  rcases p8853_3 (m.d 0 2) (by simp) with h8856 | h8856
                  · rcases p8853_3 (m.d 1 2) (by simp) with h8857 | h8857
                    · rcases p8853_3 (m.d 2 3) (by simp) with h8858 | h8858
                      · linarith only [h8858, hlam, p8853_0]
                      · rcases p8853_3 (m.d 2 4) (by simp) with h8860 | h8860
                        · linarith only [h6797, h8860, hlam]
                        · linarith only [h8474, h8860, hlam]
                    · linarith only [h8467, h8857, hlam]
                  · linarith only [h8856, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  rcases p8853_3 (m.d 0 2) (by simp) with h8865 | h8865
                  · rcases p8853_3 (m.d 1 2) (by simp) with h8866 | h8866
                    · rcases p8853_3 (m.d 2 3) (by simp) with h8867 | h8867
                      · linarith only [h6796, h8867, hlam]
                      · rcases p8853_3 (m.d 2 4) (by simp) with h8869 | h8869
                        · linarith only [h8869, hlam, p8853_0]
                        · rcases p8853_3 (m.d 2 5) (by simp) with h8871 | h8871
                          · linarith only [h6798, h8871, hlam]
                          · linarith only [h8478, h8871, hlam]
                    · linarith only [h8468, h8866, hlam]
                  · linarith only [h8865, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  rcases p8853_3 (m.d 0 2) (by simp) with h8876 | h8876
                  · rcases p8853_3 (m.d 1 2) (by simp) with h8877 | h8877
                    · rcases p8853_3 (m.d 2 3) (by simp) with h8878 | h8878
                      · linarith only [h6796, h8878, hlam]
                      · rcases p8853_3 (m.d 2 4) (by simp) with h8880 | h8880
                        · linarith only [h6797, h8880, hlam]
                        · rcases p8853_3 (m.d 2 5) (by simp) with h8882 | h8882
                          · linarith only [h8882, hlam, p8853_0]
                          · rcases h4bigk with h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c | h8884c
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h0, h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8730_1, p8884_1, u0elo1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h0, h7593, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8884_1, u0elo1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h6799, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h7593, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h6794, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h0, h6794, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8884_1, u0elo1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8470, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8472, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h6797, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8468, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8474, hlam, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8478, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8480, hc04, hc45, hlam, hphi, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8468, h8474, h8480, hc23, hc45, hlam, hphi, ht34, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8474, h8480, hc23, hc45, hlam, hphi, ht34, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h8480, hlam, p8884_0]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 4) (by simp) with h8905 | h8905
                              · linarith only [h8905, hlam, p8884_0]
                              · rcases p8884_3 (m.d 1 4) (by simp) with h8907 | h8907
                                · linarith only [h8472, h8907, hlam]
                                · rcases p8884_3 (m.d 2 4) (by simp) with h8909 | h8909
                                  · linarith only [h8478, h8909, hlam]
                                  · rcases p8884_3 (m.d 3 4) (by simp) with h8911 | h8911
                                    · linarith only [h8480, h8911, hlam]
                                    · linarith only [h6799, h8911, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 4) (by simp) with h8914 | h8914
                              · linarith only [h7593, h8914, hlam]
                              · linarith only [h6794, h8914, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              rcases p8884_3 (m.d 0 4) (by simp) with h8917 | h8917
                              · linarith only [h7593, h8917, hlam]
                              · linarith only [h6797, h8917, hlam]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [h6793, h6799, h8467, hc23, hc45, hlam, hphi, ht34, p8884_1]
                            · have p8884_0 := h8884c.1
                              have p8884_1 := h8884c.2.1
                              have p8884_2 := h8884c.2.2.1
                              have p8884_3 := h8884c.2.2.2
                              linarith only [hlam, p8884_0]
                    · linarith only [h8469, h8877, hlam]
                  · linarith only [h8876, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8761, hc12, hlam, ht01, p8853_1]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, h6793, h6799, h7593, h8467, hlam, p8730_1, p8853_2]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, h6794, h7593, h8468, hlam, p8730_1, p8853_2]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, h6795, h8469, hlam, p8730_1, p8853_2]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h6796, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8467, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8474, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8476, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h6797, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8468, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h6794, h7593, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8853_1, u0elo0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8478, hlam, p8853_1]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h6798, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h8469, hlam, p8853_0]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, h6795, h8469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8853_1, u0elo1]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p8730_1, p8853_1, u0elo1]
                · have p8853_0 := h8853c.1
                  have p8853_1 := h8853c.2.1
                  have p8853_2 := h8853c.2.2.1
                  have p8853_3 := h8853c.2.2.2
                  linarith only [hlam, p8853_0]
              · linarith only [h0, h6799, h7593, h8761, hlam, p8730_1, u0elo1]
              · linarith only [h0, h7593, h8761, hlam, p8730_1, u0elo1]
              · linarith only [h0, h8761, hlam, p8730_1, u0elo1]
      · linarith only [h6798, h8754, hlam]
    · linarith only [h6795, h8753, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6793, h8467, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, u0elo1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8951 | h8951
    · linarith only [h0, h8951, hlam]
    · linarith only [h6793, h8951, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8954 | h8954
    · linarith only [h0, h8954, hlam]
    · linarith only [h6794, h8954, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8957 | h8957
    · linarith only [h0, h8957, hlam]
    · linarith only [h6795, h8957, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6793, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6796, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6799, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h7373, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6794, hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6797, hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6793, h7593, h8467, hc23, hc45, hlam, hphi, ht34, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h7593, hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6795, hlam, p8730_0]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [h6798, hlam, p8730_1]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8972 | h8972
    · rcases p8730_3 (m.d 0 2) (by simp) with h8973 | h8973
      · rcases p8730_3 (m.d 0 3) (by simp) with h8974 | h8974
        · linarith only [h7373, h8974, hlam]
        · rcases p8730_3 (m.d 0 4) (by simp) with h8976 | h8976
          · linarith only [h7593, h8976, hlam]
          · linarith only [h6799, h8976, hlam]
      · linarith only [h6796, h8973, hlam]
    · linarith only [h6793, h8972, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    rcases p8730_3 (m.d 0 1) (by simp) with h8981 | h8981
    · rcases p8730_3 (m.d 0 2) (by simp) with h8982 | h8982
      · rcases p8730_3 (m.d 0 3) (by simp) with h8983 | h8983
        · linarith only [h7373, h8983, hlam]
        · rcases p8730_3 (m.d 0 4) (by simp) with h8985 | h8985
          · linarith only [h7593, h8985, hlam]
          · rcases p8730_3 (m.d 0 5) (by simp) with h8987 | h8987
            · rcases h0emin with h8988 | h8988 | h8988 | h8988 | h8988
              · rcases h2bigk with h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c | h8989c
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h0, hlam, p8989_1]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  rcases p8989_3 (m.d 0 2) (by simp) with h8992 | h8992
                  · rcases p8989_3 (m.d 1 2) (by simp) with h8993 | h8993
                    · rcases p8989_3 (m.d 2 3) (by simp) with h8994 | h8994
                      · linarith only [h8994, hlam, p8989_0]
                      · rcases p8989_3 (m.d 2 4) (by simp) with h8996 | h8996
                        · linarith only [h6797, h8996, hlam]
                        · linarith only [h8474, h8996, hlam]
                    · linarith only [h8467, h8993, hlam]
                  · linarith only [h8992, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  rcases p8989_3 (m.d 0 2) (by simp) with h9001 | h9001
                  · rcases p8989_3 (m.d 1 2) (by simp) with h9002 | h9002
                    · rcases p8989_3 (m.d 2 3) (by simp) with h9003 | h9003
                      · linarith only [h6796, h9003, hlam]
                      · rcases p8989_3 (m.d 2 4) (by simp) with h9005 | h9005
                        · linarith only [h9005, hlam, p8989_0]
                        · rcases p8989_3 (m.d 2 5) (by simp) with h9007 | h9007
                          · linarith only [h6798, h9007, hlam]
                          · linarith only [h8478, h9007, hlam]
                    · linarith only [h8468, h9002, hlam]
                  · linarith only [h9001, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  rcases p8989_3 (m.d 0 2) (by simp) with h9012 | h9012
                  · rcases p8989_3 (m.d 1 2) (by simp) with h9013 | h9013
                    · rcases p8989_3 (m.d 2 3) (by simp) with h9014 | h9014
                      · linarith only [h6796, h9014, hlam]
                      · rcases p8989_3 (m.d 2 4) (by simp) with h9016 | h9016
                        · linarith only [h6797, h9016, hlam]
                        · rcases p8989_3 (m.d 2 5) (by simp) with h9018 | h9018
                          · linarith only [h9018, hlam, p8989_0]
                          · rcases h4bigk with h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c | h9020c
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8467, h8470, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p9020_1, u0elo4]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h0, h6795, h8474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8730_1, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h6799, hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h7593, hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h6794, hlam, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h0, h6794, h8474, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8470, hlam, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8472, hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h6797, hlam, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8468, hlam, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8474, hlam, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8478, hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8480, hc04, hc45, hlam, hphi, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8468, h8474, h8480, hc23, hc45, hlam, hphi, ht34, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8474, h8480, hc23, hc45, hlam, hphi, ht34, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h8480, hlam, p9020_0]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              rcases p9020_3 (m.d 0 4) (by simp) with h9041 | h9041
                              · linarith only [h9041, hlam, p9020_0]
                              · rcases p9020_3 (m.d 1 4) (by simp) with h9043 | h9043
                                · linarith only [h8472, h9043, hlam]
                                · rcases p9020_3 (m.d 2 4) (by simp) with h9045 | h9045
                                  · linarith only [h8478, h9045, hlam]
                                  · rcases p9020_3 (m.d 3 4) (by simp) with h9047 | h9047
                                    · linarith only [h8480, h9047, hlam]
                                    · linarith only [h6799, h9047, hlam]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              rcases p9020_3 (m.d 0 4) (by simp) with h9050 | h9050
                              · linarith only [h7593, h9050, hlam]
                              · linarith only [h6794, h9050, hlam]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              rcases p9020_3 (m.d 0 4) (by simp) with h9053 | h9053
                              · linarith only [h7593, h9053, hlam]
                              · linarith only [h6797, h9053, hlam]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [h6793, h6799, h8467, hc23, hc45, hlam, hphi, ht34, p9020_1]
                            · have p9020_0 := h9020c.1
                              have p9020_1 := h9020c.2.1
                              have p9020_2 := h9020c.2.2.1
                              have p9020_3 := h9020c.2.2.2
                              linarith only [hlam, p9020_0]
                    · linarith only [h8469, h9013, hlam]
                  · linarith only [h9012, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h0, h8988, hc12, hlam, ht01, p8989_1]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h0, h6793, h6795, h6799, h8467, hlam, p8730_1, p8989_2]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h0, h6794, h6795, h8468, hlam, p8730_1, p8989_2]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  rcases p8989_3 (m.d 0 2) (by simp) with h9064 | h9064
                  · linarith only [h0, h9064, hlam]
                  · linarith only [h6798, h9064, hlam]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h6796, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8467, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8474, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8476, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h6797, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8468, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h6794, h6795, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p8989_1, u0elo0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8478, hlam, p8989_1]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h6798, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h8469, hlam, p8989_0]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8989_1, u0elo1]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p8989_1, u0elo1]
                · have p8989_0 := h8989c.1
                  have p8989_1 := h8989c.2.1
                  have p8989_2 := h8989c.2.2.1
                  have p8989_3 := h8989c.2.2.2
                  linarith only [hlam, p8989_0]
              · rcases h2bigk with h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c | h9082c
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h0, hlam, p9082_1]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  rcases p9082_3 (m.d 0 2) (by simp) with h9085 | h9085
                  · rcases p9082_3 (m.d 1 2) (by simp) with h9086 | h9086
                    · rcases p9082_3 (m.d 2 3) (by simp) with h9087 | h9087
                      · linarith only [h9087, hlam, p9082_0]
                      · rcases p9082_3 (m.d 2 4) (by simp) with h9089 | h9089
                        · linarith only [h6797, h9089, hlam]
                        · linarith only [h8474, h9089, hlam]
                    · linarith only [h8467, h9086, hlam]
                  · linarith only [h9085, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  rcases p9082_3 (m.d 0 2) (by simp) with h9094 | h9094
                  · rcases p9082_3 (m.d 1 2) (by simp) with h9095 | h9095
                    · rcases p9082_3 (m.d 2 3) (by simp) with h9096 | h9096
                      · linarith only [h6796, h9096, hlam]
                      · rcases p9082_3 (m.d 2 4) (by simp) with h9098 | h9098
                        · linarith only [h9098, hlam, p9082_0]
                        · rcases p9082_3 (m.d 2 5) (by simp) with h9100 | h9100
                          · linarith only [h6798, h9100, hlam]
                          · linarith only [h8478, h9100, hlam]
                    · linarith only [h8468, h9095, hlam]
                  · linarith only [h9094, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  rcases p9082_3 (m.d 0 2) (by simp) with h9105 | h9105
                  · rcases p9082_3 (m.d 1 2) (by simp) with h9106 | h9106
                    · rcases p9082_3 (m.d 2 3) (by simp) with h9107 | h9107
                      · linarith only [h6796, h9107, hlam]
                      · rcases p9082_3 (m.d 2 4) (by simp) with h9109 | h9109
                        · linarith only [h6797, h9109, hlam]
                        · rcases p9082_3 (m.d 2 5) (by simp) with h9111 | h9111
                          · linarith only [h9111, hlam, p9082_0]
                          · rcases h4bigk with h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c | h9113c
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h0, h6795, hc14, hlam, hphi, ht0b, ht45, ht5b, p8730_1, p9113_1, u0elo1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h0, h6795, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p9113_1, u0elo1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h6799, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h7593, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h6794, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h0, h6794, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9113_1, u0elo1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8470, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8472, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h6797, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8468, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8474, hlam, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8478, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h6799, h8480, hc03, hc45, hlam, hphi, ht34, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8480, hc14, hc45, hlam, hphi, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8474, h8480, hc23, hc45, hlam, hphi, ht34, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h8480, hlam, p9113_0]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 4) (by simp) with h9134 | h9134
                              · linarith only [h9134, hlam, p9113_0]
                              · rcases p9113_3 (m.d 1 4) (by simp) with h9136 | h9136
                                · linarith only [h8472, h9136, hlam]
                                · rcases p9113_3 (m.d 2 4) (by simp) with h9138 | h9138
                                  · linarith only [h8478, h9138, hlam]
                                  · rcases p9113_3 (m.d 3 4) (by simp) with h9140 | h9140
                                    · linarith only [h8480, h9140, hlam]
                                    · linarith only [h6799, h9140, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 4) (by simp) with h9143 | h9143
                              · linarith only [h7593, h9143, hlam]
                              · linarith only [h6794, h9143, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              rcases p9113_3 (m.d 0 4) (by simp) with h9146 | h9146
                              · linarith only [h7593, h9146, hlam]
                              · linarith only [h6797, h9146, hlam]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [h6793, h6799, h8467, hc23, hc45, hlam, hphi, ht34, p9113_1]
                            · have p9113_0 := h9113c.1
                              have p9113_1 := h9113c.2.1
                              have p9113_2 := h9113c.2.2.1
                              have p9113_3 := h9113c.2.2.2
                              linarith only [hlam, p9113_0]
                    · linarith only [h8469, h9106, hlam]
                  · linarith only [h9105, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h0, h6793, h6795, h6799, h8467, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8730_1, p9082_1]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h0, h6793, h6795, h6799, h8467, hlam, p8730_1, p9082_2]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h0, h6794, h6795, h8468, hlam, p8730_1, p9082_2]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  rcases p9082_3 (m.d 0 2) (by simp) with h9157 | h9157
                  · linarith only [h0, h9157, hlam]
                  · linarith only [h6798, h9157, hlam]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h6796, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8467, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8474, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8476, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h6797, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8468, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h6794, h6795, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p9082_1, u0elo0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8478, hlam, p9082_1]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h6798, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h8469, hlam, p9082_0]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9082_1, u0elo1]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p9082_1, u0elo1]
                · have p9082_0 := h9082c.1
                  have p9082_1 := h9082c.2.1
                  have p9082_2 := h9082c.2.2.1
                  have p9082_3 := h9082c.2.2.2
                  linarith only [hlam, p9082_0]
              · linarith only [h0, h6795, h6799, h8988, hlam, p8730_1, u0elo1]
              · linarith only [h0, h6795, h8988, hlam, p8730_1, u0elo1]
              · rcases h2bigk with h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c | h9177c
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h0, hlam, p9177_1]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  rcases p9177_3 (m.d 0 2) (by simp) with h9180 | h9180
                  · rcases p9177_3 (m.d 1 2) (by simp) with h9181 | h9181
                    · rcases p9177_3 (m.d 2 3) (by simp) with h9182 | h9182
                      · linarith only [h9182, hlam, p9177_0]
                      · rcases p9177_3 (m.d 2 4) (by simp) with h9184 | h9184
                        · linarith only [h6797, h9184, hlam]
                        · linarith only [h8474, h9184, hlam]
                    · linarith only [h8467, h9181, hlam]
                  · linarith only [h9180, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  rcases p9177_3 (m.d 0 2) (by simp) with h9189 | h9189
                  · rcases p9177_3 (m.d 1 2) (by simp) with h9190 | h9190
                    · rcases p9177_3 (m.d 2 3) (by simp) with h9191 | h9191
                      · linarith only [h6796, h9191, hlam]
                      · rcases p9177_3 (m.d 2 4) (by simp) with h9193 | h9193
                        · linarith only [h9193, hlam, p9177_0]
                        · rcases p9177_3 (m.d 2 5) (by simp) with h9195 | h9195
                          · linarith only [h6798, h9195, hlam]
                          · linarith only [h8478, h9195, hlam]
                    · linarith only [h8468, h9190, hlam]
                  · linarith only [h9189, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  rcases p9177_3 (m.d 0 2) (by simp) with h9200 | h9200
                  · rcases p9177_3 (m.d 1 2) (by simp) with h9201 | h9201
                    · rcases p9177_3 (m.d 2 3) (by simp) with h9202 | h9202
                      · linarith only [h6796, h9202, hlam]
                      · rcases p9177_3 (m.d 2 4) (by simp) with h9204 | h9204
                        · linarith only [h6797, h9204, hlam]
                        · rcases p9177_3 (m.d 2 5) (by simp) with h9206 | h9206
                          · linarith only [h9206, hlam, p9177_0]
                          · rcases h4bigk with h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c | h9208c
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h0, h6795, hc14, hlam, hphi, ht0b, ht45, ht5b, p8730_1, p9208_1, u0elo1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h0, h6795, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p9208_1, u0elo1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h6799, hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h7593, hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h6794, hlam, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h0, h6794, h8474, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9208_1, u0elo1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8470, hlam, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8472, hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h6797, hlam, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8468, hlam, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8474, hlam, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8478, hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h6799, h8480, hc03, hc45, hlam, hphi, ht34, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8480, hc14, hc45, hlam, hphi, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8474, h8480, hc23, hc45, hlam, hphi, ht34, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h8480, hlam, p9208_0]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              rcases p9208_3 (m.d 0 4) (by simp) with h9229 | h9229
                              · linarith only [h9229, hlam, p9208_0]
                              · rcases p9208_3 (m.d 1 4) (by simp) with h9231 | h9231
                                · linarith only [h8472, h9231, hlam]
                                · rcases p9208_3 (m.d 2 4) (by simp) with h9233 | h9233
                                  · linarith only [h8478, h9233, hlam]
                                  · rcases p9208_3 (m.d 3 4) (by simp) with h9235 | h9235
                                    · linarith only [h8480, h9235, hlam]
                                    · linarith only [h6799, h9235, hlam]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              rcases p9208_3 (m.d 0 4) (by simp) with h9238 | h9238
                              · linarith only [h7593, h9238, hlam]
                              · linarith only [h6794, h9238, hlam]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              rcases p9208_3 (m.d 0 4) (by simp) with h9241 | h9241
                              · linarith only [h7593, h9241, hlam]
                              · linarith only [h6797, h9241, hlam]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [h6793, h6799, h8467, hc23, hc45, hlam, hphi, ht34, p9208_1]
                            · have p9208_0 := h9208c.1
                              have p9208_1 := h9208c.2.1
                              have p9208_2 := h9208c.2.2.1
                              have p9208_3 := h9208c.2.2.2
                              linarith only [hlam, p9208_0]
                    · linarith only [h8469, h9201, hlam]
                  · linarith only [h9200, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h0, h6795, h8988, hc12, hlam, ht01, p9177_1]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h0, h6793, h6795, h6799, h8467, hlam, p8730_1, p9177_2]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h0, h6794, h6795, h8468, hlam, p8730_1, p9177_2]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  rcases p9177_3 (m.d 0 2) (by simp) with h9252 | h9252
                  · linarith only [h0, h9252, hlam]
                  · linarith only [h6798, h9252, hlam]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h6796, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8467, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8474, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8476, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h6797, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8468, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h6794, h6795, h8468, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8730_1, p9177_1, u0elo0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8478, hlam, p9177_1]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h6798, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h8469, hlam, p9177_0]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9177_1, u0elo1]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [h0, h6795, h8469, hc24, hlam, hphi, ht0b, ht45, ht5b, p9177_1, u0elo1]
                · have p9177_0 := h9177c.1
                  have p9177_1 := h9177c.2.1
                  have p9177_2 := h9177c.2.2.1
                  have p9177_3 := h9177c.2.2.2
                  linarith only [hlam, p9177_0]
            · linarith only [h7593, h8987, hlam]
      · linarith only [h6797, h8982, hlam]
    · linarith only [h6794, h8981, hlam]
  · have p8730_0 := h8730c.1
    have p8730_1 := h8730c.2.1
    have p8730_2 := h8730c.2.2.1
    have p8730_3 := h8730c.2.2.2
    linarith only [hlam, p8730_0]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8478 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 3 4 5 (by decide) (by decide) with h8480 | h8480
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476 h8478 h8480
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476 h8478 h8480

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 2 4 5 (by decide) (by decide) with h8478 | h8478
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476 h8478
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476 h8478

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 2 3 5 (by decide) (by decide) with h8476 | h8476
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474 h8476

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 2 3 4 (by decide) (by decide) with h8474 | h8474
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472 h8474

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 4 5 (by decide) (by decide) with h8472 | h8472
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470 h8472

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 3 4 (by decide) (by decide) with h8470 | h8470
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469 h8470

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6798, h8469, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 5 (by decide) (by decide) with h8469 | h8469
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468 h8469

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6797, h8468, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 4 (by decide) (by decide) with h8468 | h8468
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467 h8468

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6796, h8467, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 3 (by decide) (by decide) with h8467 | h8467
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h8467

end R2N4
