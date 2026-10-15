import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10684 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10685 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 4 5 (by decide) (by decide) with h10686 | h10686
  · rcases m.htr 2 3 4 (by decide) (by decide) with h10687 | h10687
    · linarith only [h10687, h8886, h8889, hlam]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h10689 | h10689
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10690 | h10690
        · rcases m.htr 3 4 5 (by decide) (by decide) with h10691 | h10691
          · rcases h2bigk with h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c | h10692c
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h0, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10695 | h10695
              · rcases p10692_3 (m.d 1 2) (by simp) with h10696 | h10696
                · rcases p10692_3 (m.d 2 3) (by simp) with h10697 | h10697
                  · linarith only [h10697, hlam, p10692_0]
                  · rcases p10692_3 (m.d 2 4) (by simp) with h10699 | h10699
                    · linarith only [h10699, h8887, hlam]
                    · linarith only [h10687, h10699, hlam]
                · linarith only [h10682, h10696, hlam]
              · linarith only [h10695, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10704 | h10704
              · rcases p10692_3 (m.d 1 2) (by simp) with h10705 | h10705
                · rcases p10692_3 (m.d 2 3) (by simp) with h10706 | h10706
                  · linarith only [h10706, h8886, hlam]
                  · rcases p10692_3 (m.d 2 4) (by simp) with h10708 | h10708
                    · linarith only [h10708, hlam, p10692_0]
                    · rcases p10692_3 (m.d 2 5) (by simp) with h10710 | h10710
                      · linarith only [h10710, h8888, hlam]
                      · rcases h4bigk with h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c | h10712c
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h6874, hlam, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h8889, hlam, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, h6874, hc01, hc12, hlam, hphi, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, h10687, h10689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, h10689, h8886, h8889, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          rcases p10712_3 (m.d 0 4) (by simp) with h10722 | h10722
                          · linarith only [h10722, h6874, hlam]
                          · linarith only [h10681, h10722, hlam]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h8887, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10683, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10687, hlam, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10692_1, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10689, h10691, h8886, h8889, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10685, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10682, h10685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10712_1]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10681, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10686, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10690, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [h10691, hlam, p10712_0]
                        · have p10712_0 := h10712c.1
                          have p10712_1 := h10712c.2.1
                          have p10712_2 := h10712c.2.2.1
                          have p10712_3 := h10712c.2.2.2
                          linarith only [hlam, p10712_0]
                · linarith only [h10683, h10705, hlam]
              · linarith only [h10704, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10742 | h10742
              · rcases p10692_3 (m.d 1 2) (by simp) with h10743 | h10743
                · rcases p10692_3 (m.d 2 3) (by simp) with h10744 | h10744
                  · linarith only [h10744, h8886, hlam]
                  · linarith only [h10689, h10744, hlam]
                · linarith only [h10684, h10743, hlam]
              · linarith only [h10742, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10689, h10691, h8886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10692_1]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10751 | h10751
              · linarith only [h0, h10751, hlam]
              · linarith only [h10751, h8886, hlam]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10754 | h10754
              · linarith only [h0, h10754, hlam]
              · linarith only [h10754, h8887, hlam]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10757 | h10757
              · linarith only [h0, h10757, hlam]
              · linarith only [h10757, h8888, hlam]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h8886, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10682, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10687, hlam, p10692_1]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10682, h10685, h8886, h8889, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10692_1]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h8887, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10683, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10682, h10685, h10689, h10691, h8887, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10692_1]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              rcases p10692_3 (m.d 0 2) (by simp) with h10769 | h10769
              · rcases p10692_3 (m.d 1 2) (by simp) with h10770 | h10770
                · rcases p10692_3 (m.d 2 3) (by simp) with h10771 | h10771
                  · linarith only [h10687, h10771, hlam]
                  · linarith only [h10689, h10771, hlam]
                · linarith only [h10684, h10770, hlam]
              · linarith only [h10769, h8888, hlam]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h8888, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10684, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10689, hlam, p10692_0]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [h10690, hlam, p10692_1]
            · have p10692_0 := h10692c.1
              have p10692_1 := h10692c.2.1
              have p10692_2 := h10692c.2.2.1
              have p10692_3 := h10692c.2.2.2
              linarith only [hlam, p10692_0]
          · linarith only [h10681, h10689, h10691, h8886, h8889, hc04, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h10681, h10682, h10685, h10687, h10689, h10690, h8889, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10783 | h10783
        · rcases m.htr 3 4 5 (by decide) (by decide) with h10784 | h10784
          · rcases h2bigk with h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c | h10785c
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h0, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10788 | h10788
              · rcases p10785_3 (m.d 1 2) (by simp) with h10789 | h10789
                · rcases p10785_3 (m.d 2 3) (by simp) with h10790 | h10790
                  · linarith only [h10790, hlam, p10785_0]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10792 | h10792
                    · linarith only [h10792, h8887, hlam]
                    · linarith only [h10687, h10792, hlam]
                · linarith only [h10682, h10789, hlam]
              · linarith only [h10788, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10797 | h10797
              · rcases p10785_3 (m.d 1 2) (by simp) with h10798 | h10798
                · rcases p10785_3 (m.d 2 3) (by simp) with h10799 | h10799
                  · linarith only [h10799, h8886, hlam]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10801 | h10801
                    · linarith only [h10801, hlam, p10785_0]
                    · rcases p10785_3 (m.d 2 5) (by simp) with h10803 | h10803
                      · linarith only [h10803, h8888, hlam]
                      · rcases h4bigk with h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c | h10805c
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h6874, hlam, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, h10689, h10783, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h8889, hlam, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, h6874, hc01, hc12, hlam, hphi, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, h10783, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          rcases p10805_3 (m.d 0 4) (by simp) with h10815 | h10815
                          · linarith only [h10815, h6874, hlam]
                          · linarith only [h10681, h10815, hlam]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h8887, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10683, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10687, hlam, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10785_1, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10685, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10682, h10685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10805_1]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10681, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10686, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10783, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [h10784, hlam, p10805_0]
                        · have p10805_0 := h10805c.1
                          have p10805_1 := h10805c.2.1
                          have p10805_2 := h10805c.2.2.1
                          have p10805_3 := h10805c.2.2.2
                          linarith only [hlam, p10805_0]
                · linarith only [h10683, h10798, hlam]
              · linarith only [h10797, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10835 | h10835
              · rcases p10785_3 (m.d 1 2) (by simp) with h10836 | h10836
                · rcases p10785_3 (m.d 2 3) (by simp) with h10837 | h10837
                  · linarith only [h10837, h8886, hlam]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10839 | h10839
                    · linarith only [h10839, h8887, hlam]
                    · linarith only [h10783, h10839, hlam]
                · linarith only [h10684, h10836, hlam]
              · linarith only [h10835, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10783, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10785_1]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10846 | h10846
              · linarith only [h0, h10846, hlam]
              · linarith only [h10846, h8886, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10849 | h10849
              · linarith only [h0, h10849, hlam]
              · linarith only [h10849, h8887, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10852 | h10852
              · linarith only [h0, h10852, hlam]
              · linarith only [h10852, h8888, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h8886, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10682, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10687, hlam, p10785_1]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10689, hlam, p10785_1]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h8887, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10683, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10862 | h10862
              · rcases p10785_3 (m.d 1 2) (by simp) with h10863 | h10863
                · rcases p10785_3 (m.d 2 3) (by simp) with h10864 | h10864
                  · linarith only [h10687, h10864, hlam]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10866 | h10866
                    · rcases p10785_3 (m.d 2 5) (by simp) with h10867 | h10867
                      · linarith only [h10783, h10867, hlam]
                      · linarith only [h10689, h10867, hlam]
                    · linarith only [h10687, h10866, hlam]
                · linarith only [h10682, h10863, hlam]
              · linarith only [h10862, h8886, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10874 | h10874
              · rcases p10785_3 (m.d 1 2) (by simp) with h10875 | h10875
                · rcases p10785_3 (m.d 2 3) (by simp) with h10876 | h10876
                  · linarith only [h10687, h10876, hlam]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10878 | h10878
                    · rcases p10785_3 (m.d 2 5) (by simp) with h10879 | h10879
                      · linarith only [h10783, h10879, hlam]
                      · rcases h4bigk with h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c | h10881c
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h6874, hlam, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10689, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10785_1, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h8889, hlam, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, h6874, hc01, hc12, hlam, hphi, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, h10689, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10785_1, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          rcases p10881_3 (m.d 0 4) (by simp) with h10891 | h10891
                          · linarith only [h10891, h6874, hlam]
                          · linarith only [h10681, h10891, hlam]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h8887, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10683, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10687, hlam, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h8887, hc02, hc45, hlam, hphi, ht0b, ht5b, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10685, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10682, h10685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10881_1]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10681, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10686, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10783, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [h10784, hlam, p10881_0]
                        · have p10881_0 := h10881c.1
                          have p10881_1 := h10881c.2.1
                          have p10881_2 := h10881c.2.2.1
                          have p10881_3 := h10881c.2.2.2
                          linarith only [hlam, p10881_0]
                    · linarith only [h10783, h10878, hlam]
                · linarith only [h10684, h10875, hlam]
              · linarith only [h10874, h8888, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h8888, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10684, hlam, p10785_0]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              rcases p10785_3 (m.d 0 2) (by simp) with h10914 | h10914
              · rcases p10785_3 (m.d 1 2) (by simp) with h10915 | h10915
                · rcases p10785_3 (m.d 2 3) (by simp) with h10916 | h10916
                  · linarith only [h10689, h10916, hlam]
                  · rcases p10785_3 (m.d 2 4) (by simp) with h10918 | h10918
                    · rcases p10785_3 (m.d 2 5) (by simp) with h10919 | h10919
                      · rcases h4bigk with h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c | h10920c
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h6874, hlam, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h8889, hlam, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, h8889, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, h6874, hc01, hc12, hlam, hphi, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, h10783, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          rcases p10920_3 (m.d 0 4) (by simp) with h10930 | h10930
                          · linarith only [h10930, h6874, hlam]
                          · linarith only [h10681, h10930, hlam]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h8887, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10683, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10687, hlam, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h0, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10681, h8888, hc23, hc34, hlam, hphi, p10785_1, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10685, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10682, h10685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10920_1]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10681, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10686, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10783, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [h10784, hlam, p10920_0]
                        · have p10920_0 := h10920c.1
                          have p10920_1 := h10920c.2.1
                          have p10920_2 := h10920c.2.2.1
                          have p10920_3 := h10920c.2.2.2
                          linarith only [hlam, p10920_0]
                      · linarith only [h10689, h10919, hlam]
                    · linarith only [h10687, h10918, hlam]
                · linarith only [h10682, h10915, hlam]
              · linarith only [h10914, h8886, hlam]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [h10783, hlam, p10785_1]
            · have p10785_0 := h10785c.1
              have p10785_1 := h10785c.2.1
              have p10785_2 := h10785c.2.2.1
              have p10785_3 := h10785c.2.2.2
              linarith only [hlam, p10785_0]
          · linarith only [h10681, h10784, h8889, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h10955 | h10955
          · rcases h2bigk with h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c | h10956c
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h0, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              rcases p10956_3 (m.d 0 2) (by simp) with h10959 | h10959
              · rcases p10956_3 (m.d 1 2) (by simp) with h10960 | h10960
                · rcases p10956_3 (m.d 2 3) (by simp) with h10961 | h10961
                  · linarith only [h10961, hlam, p10956_0]
                  · rcases p10956_3 (m.d 2 4) (by simp) with h10963 | h10963
                    · linarith only [h10963, h8887, hlam]
                    · linarith only [h10687, h10963, hlam]
                · linarith only [h10682, h10960, hlam]
              · linarith only [h10959, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              rcases p10956_3 (m.d 0 2) (by simp) with h10968 | h10968
              · rcases p10956_3 (m.d 1 2) (by simp) with h10969 | h10969
                · rcases p10956_3 (m.d 2 3) (by simp) with h10970 | h10970
                  · linarith only [h10970, h8886, hlam]
                  · rcases p10956_3 (m.d 2 4) (by simp) with h10972 | h10972
                    · linarith only [h10972, hlam, p10956_0]
                    · rcases p10956_3 (m.d 2 5) (by simp) with h10974 | h10974
                      · linarith only [h10974, h8888, hlam]
                      · linarith only [h10783, h10974, hlam]
                · linarith only [h10683, h10969, hlam]
              · linarith only [h10968, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              rcases p10956_3 (m.d 0 2) (by simp) with h10979 | h10979
              · rcases p10956_3 (m.d 1 2) (by simp) with h10980 | h10980
                · rcases p10956_3 (m.d 2 3) (by simp) with h10981 | h10981
                  · linarith only [h10981, h8886, hlam]
                  · rcases p10956_3 (m.d 2 4) (by simp) with h10983 | h10983
                    · linarith only [h10983, h8887, hlam]
                    · rcases p10956_3 (m.d 2 5) (by simp) with h10985 | h10985
                      · linarith only [h10985, hlam, p10956_0]
                      · rcases h4bigk with h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c | h10987c
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h6874, hlam, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10687, h8889, hc23, hc34, hlam, hphi, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h8889, hlam, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10687, h10783, h8889, hc23, hc34, hlam, hphi, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10682, h10685, h6874, hc01, hc12, hlam, hphi, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          rcases p10987_3 (m.d 0 4) (by simp) with h10995 | h10995
                          · linarith only [h10995, h6874, hlam]
                          · linarith only [h10995, h8887, hlam]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10682, h10685, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10682, h10685, h10687, h10783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h8887, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10683, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10687, hlam, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10783, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10681, h10687, h10783, hc23, hc34, hlam, hphi, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10685, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10682, h10685, h10687, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10682, h10685, h10687, h10783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10681, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10686, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10681, h10687, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10987_1]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [h10955, hlam, p10987_0]
                        · have p10987_0 := h10987c.1
                          have p10987_1 := h10987c.2.1
                          have p10987_2 := h10987c.2.2.1
                          have p10987_3 := h10987c.2.2.2
                          linarith only [hlam, p10987_0]
                · linarith only [h10684, h10980, hlam]
              · linarith only [h10979, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10687, h10783, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10682, h10685, h10687, h10783, h8889, hlam, p10956_2]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10682, h10685, h10783, h8889, hlam, p10956_2]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              rcases p10956_3 (m.d 0 2) (by simp) with h11021 | h11021
              · linarith only [h0, h11021, hlam]
              · linarith only [h11021, h8888, hlam]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h8886, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10682, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10687, hlam, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10689, hlam, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h8887, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10683, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10682, h10685, h10783, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10783, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h8888, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10684, hlam, p10956_0]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10682, h10685, h10783, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [h10681, h10682, h10685, h10783, h8889, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10956_1]
            · have p10956_0 := h10956c.1
              have p10956_1 := h10956c.2.1
              have p10956_2 := h10956c.2.2.1
              have p10956_3 := h10956c.2.2.2
              linarith only [hlam, p10956_0]
          · linarith only [h10681, h10955, h8889, hlam]
  · linarith only [h10681, h10682, h10685, h10686, h6874, h8889, hc01, hc12, hlam, hphi]

end R2N4
