import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S11
import Jsp000404.R1LeavesN7_6S18
import Jsp000404.R1LeavesN7_6S28
import Jsp000404.R1LeavesN7_6S29

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12982000 in
set_option maxHeartbeats 12982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s10_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10058 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h10059 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h10682 | h10682
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10683 | h10683
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10684 | h10684
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10685 | h10685
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10686 | h10686
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10687 | h10687
            · linarith only [h10058, h10059, h10687, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10689 | h10689
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10690 | h10690
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10691 | h10691
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10692 | h10692
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10693 | h10693
                      · linarith only [h10058, h10687, h10693, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10695 | h10695
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10696 | h10696
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10697 | h10697
                            · linarith only [h10058, h10059, h10690, h10693, h10697, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10699 | h10699
                              · linarith only [h10059, h10682, h10693, h10695, h10699, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases h0bigk with h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c | h10701c
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h0, hlam, p10701_1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h6793, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10059, h10690, h10693, h10695, hc34, hc45, hlam, hphi, p10701_1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10059, hlam, p10701_1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10690, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10690, h10695, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  rcases p10701_3 (m.d 0 1) (by simp) with h10710 | h10710
                                  · linarith only [h0, h10710, hlam]
                                  · linarith only [h10058, h10710, hlam]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10059, h10690, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10690, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo2]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10682, hlam, p10701_1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  rcases p10701_3 (m.d 0 1) (by simp) with h10717 | h10717
                                  · linarith only [h10717, h6793, hlam]
                                  · linarith only [h10058, h10717, hlam]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10059, h10682, h10690, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10683, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10685, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10687, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10058, h10690, h10695, hc34, hlam, hphi, ht0b, ht45, ht5b, p10701_1, u0elo4]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10684, hlam, p10701_1]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [h10686, hlam, p10701_0]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  rcases p10701_3 (m.d 0 1) (by simp) with h10729 | h10729
                                  · linarith only [h10059, h10729, hlam]
                                  · linarith only [h10058, h10729, hlam]
                                · have p10701_0 := h10701c.1
                                  have p10701_1 := h10701c.2.1
                                  have p10701_2 := h10701c.2.2.1
                                  have p10701_3 := h10701c.2.2.2
                                  linarith only [hlam, p10701_0]
                          · linarith only [h10682, h10686, h10695, h10696, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h10058, h10059, h10692, h10693, h10695, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h10058, h10685, h10692, h6793, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10684, h10691, hlam]
                · linarith only [h0, h10683, h10690, hlam]
              · linarith only [h0, h10682, h10689, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10739 | h10739
            · linarith only [h10058, h10686, h10739, h6793, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10741 | h10741
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10742 | h10742
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10743 | h10743
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10744 | h10744
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10745 | h10745
                      · linarith only [h10058, h10739, h10745, h6793, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10747 | h10747
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10748 | h10748
                          · linarith only [h10682, h10686, h10748, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10750 | h10750
                            · linarith only [h10058, h10059, h10742, h10745, h10750, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10752 | h10752
                              · linarith only [h10058, h10059, h10742, h10745, h10747, h10752, hlam]
                              · rcases h0bigk with h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c | h10754c
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h0, hlam, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h6793, hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10686, h10752, h6793, hc04, hc45, hlam, hphi, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10059, hlam, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10742, h10747, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10742, h10747, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  rcases p10754_3 (m.d 0 1) (by simp) with h10763 | h10763
                                  · linarith only [h0, h10763, hlam]
                                  · linarith only [h10058, h10763, hlam]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10686, h10742, h10747, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10742, h10747, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo2]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10682, hlam, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10686, h10742, h10747, h10752, hc34, hc45, hlam, hphi, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10686, hlam, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10683, hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10685, hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10739, hlam, p10754_0]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10684, h10742, h10747, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10684, hlam, p10754_1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [h10058, h10684, h10742, h10747, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, p10754_1, u0elo1]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  rcases p10754_3 (m.d 0 1) (by simp) with h10780 | h10780
                                  · linarith only [h10059, h10780, hlam]
                                  · linarith only [h10058, h10780, hlam]
                                · have p10754_0 := h10754c.1
                                  have p10754_1 := h10754c.2.1
                                  have p10754_2 := h10754c.2.2.1
                                  have p10754_3 := h10754c.2.2.2
                                  linarith only [hlam, p10754_0]
                        · linarith only [h10685, h10686, h10747, hc23, hc35, hlam, hphi]
                    · linarith only [h10058, h10685, h10744, h6793, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10684, h10743, hlam]
                · linarith only [h0, h10683, h10742, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h10682, h10741, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h10058, h10685, h6793, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10790 | h10790
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10791 | h10791
          · linarith only [h10682, h10684, h10791, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10793 | h10793
            · linarith only [h0, h10058, h10684, h10793, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10795 | h10795
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10796 | h10796
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10797 | h10797
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10798 | h10798
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10799 | h10799
                      · linarith only [h10058, h10682, h10684, h10793, h10797, h10799, h6793, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10801 | h10801
                        · linarith only [h10682, h10684, h10797, h10801, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10682, h10684, h10790, h10797, h10801, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10058, h10790, h10798, h6793, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10805 | h10805
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10806 | h10806
                      · linarith only [h0, h10058, h10797, h10806, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10808 | h10808
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10809 | h10809
                          · linarith only [h10058, h10682, h10791, h10796, h10808, h10809, h6793, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10811 | h10811
                            · linarith only [h0, h10058, h10796, h10797, h10806, h10809, h10811, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h10058, h10795, h10796, h10797, h10808, h10811, h6793, hc34, hc45, hlam, hphi]
                        · linarith only [h10790, h10791, h10808, hc23, hc35, hlam, hphi]
                    · linarith only [h10790, h10791, h10805, hc13, hc35, hlam, hphi]
                · linarith only [h0, h10683, h10796, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h10682, h10795, hlam]
        · linarith only [h10058, h10790, h6793, hlam]
    · linarith only [h0, h10058, h10683, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h10820 | h10820
    · rcases m.htr 0 2 5 (by decide) (by decide) with h10821 | h10821
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10822 | h10822
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10823 | h10823
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10824 | h10824
            · linarith only [h10058, h10059, h10824, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10826 | h10826
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10827 | h10827
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10828 | h10828
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10829 | h10829
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10830 | h10830
                      · linarith only [h10058, h10824, h10830, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10832 | h10832
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10833 | h10833
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10834 | h10834
                            · linarith only [h10058, h10059, h10827, h10830, h10834, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10836 | h10836
                              · linarith only [h10058, h10059, h10827, h10830, h10832, h10836, hlam]
                              · rcases h0bigk with h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c | h10838c
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h0, hlam, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h6793, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10059, h10682, h10821, h10826, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10059, hlam, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10682, h10826, hc01, hc12, hlam, hphi, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10682, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, h10682, h10826, h10827, h10832, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10682, h10826, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, h10827, h10832, hc34, hlam, hphi, ht0b, ht45, ht5b, p10838_1, u0elo2]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10682, h10821, h10826, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  rcases p10838_3 (m.d 0 1) (by simp) with h10852 | h10852
                                  · linarith only [h10852, h6793, hlam]
                                  · linarith only [h10058, h10852, hlam]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, h10059, h10682, h10826, h10827, h10832, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10820, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10822, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10824, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, h10821, h10827, h10832, hc34, hlam, hphi, ht0b, ht45, ht5b, p10838_1, u0elo1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10821, hlam, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10823, hlam, p10838_0]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [h10058, h10682, h10821, h10826, h10827, h10832, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10838_1]
                                · have p10838_0 := h10838c.1
                                  have p10838_1 := h10838c.2.1
                                  have p10838_2 := h10838c.2.2.1
                                  have p10838_3 := h10838c.2.2.2
                                  linarith only [hlam, p10838_0]
                          · linarith only [h10682, h10823, h10833, hlam]
                        · linarith only [h10682, h10822, h10832, hlam]
                    · linarith only [h10058, h10059, h10682, h10821, h10822, h10826, h10827, h10829, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h10682, h10821, h10828, hc12, hc23, hlam, hphi]
                · linarith only [h10059, h10682, h10821, h10826, h10827, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10871 | h10871
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10872 | h10872
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10873 | h10873
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10874 | h10874
                      · linarith only [h10058, h10059, h10826, h10872, h10874, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10876 | h10876
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10877 | h10877
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10878 | h10878
                            · linarith only [h10058, h10059, h10871, h10874, h10878, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10880 | h10880
                              · linarith only [h10058, h10059, h10871, h10874, h10876, h10880, hlam]
                              · rcases h0bigk with h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c | h10882c
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h0, hlam, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h6793, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10059, h10826, h10872, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10059, hlam, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h0, h10826, hc01, hc23, hlam, hphi, ht12, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10682, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  rcases p10882_3 (m.d 0 1) (by simp) with h10891 | h10891
                                  · linarith only [h0, h10891, hlam]
                                  · linarith only [h10058, h10891, hlam]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h0, h10058, h10059, h10826, h10871, h10876, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10058, h10871, h10876, hc34, hlam, hphi, ht0b, ht45, ht5b, p10882_1, u0elo2]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10821, hc25, hlam, hphi, ht0b, ht5b, p10882_1, u0elo2]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  rcases p10882_3 (m.d 0 1) (by simp) with h10898 | h10898
                                  · linarith only [h10898, h6793, hlam]
                                  · linarith only [h10058, h10898, hlam]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10058, h10059, h10871, h10876, hc34, hlam, hphi, ht0b, ht45, ht5b, p10882_1, u0elo2]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10058, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10820, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10822, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10824, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10058, h10821, h10871, h10876, hc34, hlam, hphi, ht0b, ht45, ht5b, p10882_1, u0elo1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10821, hlam, p10882_1]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [h10823, hlam, p10882_0]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  rcases p10882_3 (m.d 0 1) (by simp) with h10910 | h10910
                                  · linarith only [h10059, h10910, hlam]
                                  · linarith only [h10058, h10910, hlam]
                                · have p10882_0 := h10882c.1
                                  have p10882_1 := h10882c.2.1
                                  have p10882_2 := h10882c.2.2.1
                                  have p10882_3 := h10882c.2.2.2
                                  linarith only [hlam, p10882_0]
                          · linarith only [h0, h10058, h10826, h10871, h10876, h10877, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h10058, h10059, h10826, h10871, h10872, h10876, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h10058, h10822, h10871, h10873, h6793, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10821, h10872, hlam]
                · linarith only [h0, h10820, h10871, hlam]
          · linarith only [h10682, h10821, h10823, hlam]
        · linarith only [h0, h10058, h10682, h10822, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h10921 | h10921
        · rcases m.htr 0 3 5 (by decide) (by decide) with h10922 | h10922
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10923 | h10923
            · linarith only [h0, h10058, h10821, h10923, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10925 | h10925
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10926 | h10926
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10927 | h10927
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10928 | h10928
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10929 | h10929
                      · linarith only [h0, h10058, h10682, h10923, h10925, h10929, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10931 | h10931
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10932 | h10932
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10933 | h10933
                            · linarith only [h0, h10058, h10821, h10926, h10927, h10929, h10933, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h10935 | h10935
                              · linarith only [h0, h10058, h10821, h10926, h10927, h10929, h10931, h10935, hlam]
                              · rcases h0bigk with h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c | h10937c
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h0, hlam, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h6793, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h0, h10821, h10925, h10932, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10059, hlam, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10821, h10925, h10932, hc01, hc12, hlam, hphi, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10682, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10058, h10821, h10925, h10926, h10931, h10932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10821, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10058, h10926, h10931, hc34, hlam, hphi, ht0b, ht45, ht5b, p10937_1, u0elo2]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h0, h10058, h10682, h10925, h10926, h10931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  rcases p10937_3 (m.d 0 1) (by simp) with h10951 | h10951
                                  · linarith only [h10951, h6793, hlam]
                                  · linarith only [h10058, h10951, hlam]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h0, h10058, h10682, h10821, h10925, h10926, h10931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10058, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10820, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10921, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10923, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10058, h10926, h10931, hc34, hlam, hphi, ht0b, ht45, ht5b, p10937_1, u0elo4]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h0, h10058, h10821, h10925, h10926, h10931, h10932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10937_1]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [h10922, hlam, p10937_0]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  rcases p10937_3 (m.d 0 1) (by simp) with h10963 | h10963
                                  · linarith only [h10059, h10963, hlam]
                                  · linarith only [h10058, h10963, hlam]
                                · have p10937_0 := h10937c.1
                                  have p10937_1 := h10937c.2.1
                                  have p10937_2 := h10937c.2.2.1
                                  have p10937_3 := h10937c.2.2.2
                                  linarith only [hlam, p10937_0]
                          · linarith only [h10682, h10922, h10932, hlam]
                        · linarith only [h10682, h10921, h10931, hlam]
                    · linarith only [h0, h10058, h10682, h10921, h10925, h10926, h10928, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h10058, h10682, h10925, h10926, h10927, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h10058, h10682, h10925, h10926, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10972 | h10972
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10973 | h10973
                  · linarith only [h0, h10058, h10821, h10925, h10972, h10973, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10975 | h10975
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10976 | h10976
                      · linarith only [h0, h10058, h10925, h10976, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10978 | h10978
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10979 | h10979
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10980 | h10980
                            · linarith only [h0, h10058, h10059, h10972, h10973, h10976, h10979, h10980, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h10058, h10973, h10980, hc14, hc45, hlam, hphi]
                          · linarith only [h10682, h10922, h10979, hlam]
                        · linarith only [h0, h10058, h10925, h10972, h10978, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h10058, h10921, h10975, h6793, hlam]
                · linarith only [h0, h10820, h10972, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h10987 | h10987
            · linarith only [h10058, h10922, h10987, h6793, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h10989 | h10989
              · rcases m.htr 1 2 4 (by decide) (by decide) with h10990 | h10990
                · rcases m.htr 1 2 5 (by decide) (by decide) with h10991 | h10991
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h10992 | h10992
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10993 | h10993
                      · linarith only [h10058, h10987, h10993, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h10995 | h10995
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h10996 | h10996
                          · linarith only [h10058, h10922, h10989, h10990, h10995, h10996, h6793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h10998 | h10998
                            · linarith only [h10058, h10059, h10990, h10993, h10998, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h11000 | h11000
                              · linarith only [h0, h10058, h10682, h10990, h10991, h10993, h10995, h10996, h11000, hlam]
                              · linarith only [h0, h10058, h10682, h10990, h10995, h10996, h11000, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h10058, h10682, h10921, h10990, h10995, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h10058, h10921, h10990, h10992, h6793, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h10682, h10989, h10991, hc02, hc25, hlam, hphi]
                · linarith only [h0, h10058, h10682, h10989, h10990, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h11007 | h11007
                · rcases m.htr 1 2 5 (by decide) (by decide) with h11008 | h11008
                  · linarith only [h0, h10058, h10821, h10989, h11007, h11008, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11010 | h11010
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h11011 | h11011
                      · linarith only [h0, h10058, h10989, h11011, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11013 | h11013
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h11014 | h11014
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h11015 | h11015
                            · linarith only [h0, h10058, h10682, h10922, h11007, h11008, h11011, h11014, h11015, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h10058, h11007, h11008, h11013, h11015, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h10058, h10989, h11007, h11013, h11014, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h10058, h10989, h11007, h11013, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h10058, h10921, h10989, h11007, h11010, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h10820, h11007, hlam]
        · linarith only [h10058, h10921, h6793, hlam]
    · linarith only [h0, h10058, h10820, hlam]

set_option maxHeartbeats 12982000 in
set_option maxHeartbeats 12982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s10_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10058 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h10059 | h10059
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s10_x0_x0 m hb0 hb2 hb4 hg0 hg6793 h10058 h10059
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s10_x0_x1 m hb0 hb2 hb4 hg0 hg6793 h10058 h10059

set_option maxHeartbeats 12982000 in
set_option maxHeartbeats 12982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s10_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  exact r1l7_20_12_14_M_LI_L_I_L_I_s11 m hb0 hb2 hb4 h0 h6793 h10058

set_option maxHeartbeats 12982000 in
set_option maxHeartbeats 12982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s10 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h10058 | h10058
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s10_x0 m hb0 hb2 hb4 hg0 hg6793 h10058
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s10_x1 m hb0 hb2 hb4 hg0 hg6793 h10058

set_option maxHeartbeats 19512000 in
set_option maxHeartbeats 19512000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h6793 | h6793
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s8 m hb0 hb2 hb4 h0 h6793
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s10 m hb0 hb2 hb4 h0 h6793

set_option maxHeartbeats 33098000 in
set_option maxHeartbeats 33098000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s7 m hb0 hb2 hb4 h0

end R2N4
