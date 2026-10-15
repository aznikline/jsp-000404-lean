import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12274000 in
set_option maxHeartbeats 12274000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s24_x1_x1_x1_x1_x1_x0_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h23338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h28544 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h28546 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h28548 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h28550 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h28552 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h28553 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h28555 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h28557 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h28558 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  rcases m.htr 2 4 5 (by decide) (by decide) with h28559 | h28559
  · rcases m.htr 3 4 5 (by decide) (by decide) with h28560 | h28560
    · linarith only [h1, h23338, h28544, h28552, h28558, h28560, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
    · rcases h1bigk with h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c | h28562c
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        rcases p28562_3 (m.d 0 1) (by simp) with h28564 | h28564
        · rcases p28562_3 (m.d 1 2) (by simp) with h28565 | h28565
          · linarith only [h28565, hlam, p28562_0]
          · rcases p28562_3 (m.d 1 3) (by simp) with h28567 | h28567
            · linarith only [h1, h28567, hlam]
            · linarith only [h28546, h28567, hlam]
        · linarith only [h28564, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        rcases p28562_3 (m.d 0 1) (by simp) with h28571 | h28571
        · rcases p28562_3 (m.d 1 2) (by simp) with h28572 | h28572
          · linarith only [h0, h28572, hlam]
          · rcases p28562_3 (m.d 1 3) (by simp) with h28574 | h28574
            · linarith only [h28574, hlam, p28562_0]
            · rcases p28562_3 (m.d 1 4) (by simp) with h28576 | h28576
              · linarith only [h2, h28576, hlam]
              · rcases p28562_3 (m.d 1 5) (by simp) with h28578 | h28578
                · linarith only [h28578, h3, hlam]
                · linarith only [h28553, h28578, hlam]
        · linarith only [h28571, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        rcases p28562_3 (m.d 0 1) (by simp) with h28582 | h28582
        · rcases p28562_3 (m.d 1 2) (by simp) with h28583 | h28583
          · linarith only [h0, h28583, hlam]
          · rcases p28562_3 (m.d 1 3) (by simp) with h28585 | h28585
            · linarith only [h1, h28585, hlam]
            · linarith only [h28552, h28585, hlam]
        · linarith only [h28582, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        rcases p28562_3 (m.d 0 1) (by simp) with h28589 | h28589
        · rcases p28562_3 (m.d 1 2) (by simp) with h28590 | h28590
          · linarith only [h0, h28590, hlam]
          · rcases p28562_3 (m.d 1 3) (by simp) with h28592 | h28592
            · linarith only [h1, h28592, hlam]
            · rcases p28562_3 (m.d 1 4) (by simp) with h28594 | h28594
              · linarith only [h2, h28594, hlam]
              · rcases p28562_3 (m.d 1 5) (by simp) with h28596 | h28596
                · linarith only [h28596, hlam, p28562_0]
                · rcases h1emax with h28598 | h28598 | h28598 | h28598 | h28598
                  · linarith only [h1, h28552, h28598, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h2bigk with h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c | h28600c
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h4, hc12, hc23, hlam, hphi, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h4, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h19744, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h22010, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h0, hlam, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28546, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28548, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28550, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28611 | h28611
                      · linarith only [h28611, hlam, p28600_0]
                      · rcases p28600_3 (m.d 1 2) (by simp) with h28613 | h28613
                        · linarith only [h28546, h28613, hlam]
                        · rcases p28600_3 (m.d 2 3) (by simp) with h28615 | h28615
                          · rcases p28600_3 (m.d 2 4) (by simp) with h28616 | h28616
                            · linarith only [h28557, h28616, hlam]
                            · linarith only [h19744, h28616, hlam]
                          · linarith only [h28615, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28620 | h28620
                      · linarith only [h28620, h4, hlam]
                      · linarith only [h0, h28620, hlam]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h19744, h23337, h23338, h28559, h28560, hc02, hc23, hlam, hphi, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h1, h23338, h28552, h28559, h28560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28626 | h28626
                      · linarith only [h28626, hlam, p28600_0]
                      · rcases p28600_3 (m.d 1 2) (by simp) with h28628 | h28628
                        · linarith only [h28548, h28628, hlam]
                        · rcases p28600_3 (m.d 2 3) (by simp) with h28630 | h28630
                          · rcases p28600_3 (m.d 2 4) (by simp) with h28631 | h28631
                            · rcases p28600_3 (m.d 2 5) (by simp) with h28632 | h28632
                              · linarith only [h28559, h28632, hlam]
                              · linarith only [h22010, h28632, hlam]
                            · linarith only [h28631, hlam, p28600_0]
                          · linarith only [h28630, h4, hlam]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28637 | h28637
                      · linarith only [h19744, h28637, hlam]
                      · linarith only [h0, h28637, hlam]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28557, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h1, h23338, h28552, h28559, h28560, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28643 | h28643
                      · linarith only [h28643, hlam, p28600_0]
                      · rcases p28600_3 (m.d 1 2) (by simp) with h28645 | h28645
                        · linarith only [h28550, h28645, hlam]
                        · rcases p28600_3 (m.d 2 3) (by simp) with h28647 | h28647
                          · rcases p28600_3 (m.d 2 4) (by simp) with h28648 | h28648
                            · rcases p28600_3 (m.d 2 5) (by simp) with h28649 | h28649
                              · rcases h4bigk with h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c | h28650c
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h23337, h23338, h28548, hc12, hc35, hlam, hphi, ht23, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h19744, hlam, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28544, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h2, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28548, hlam, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h2, h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28555, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  rcases p28650_3 (m.d 0 4) (by simp) with h28661 | h28661
                                  · linarith only [h19744, h28661, hlam]
                                  · rcases p28650_3 (m.d 1 4) (by simp) with h28663 | h28663
                                    · linarith only [h28548, h28663, hlam]
                                    · rcases p28650_3 (m.d 2 4) (by simp) with h28665 | h28665
                                      · rcases p28650_3 (m.d 3 4) (by simp) with h28666 | h28666
                                        · linarith only [h28557, h28666, hlam]
                                        · rcases p28650_3 (m.d 4 5) (by simp) with h28668 | h28668
                                          · linarith only [h28559, h28668, hlam]
                                          · linarith only [h28544, h28668, hlam]
                                      · linarith only [h19744, h28665, hlam]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  rcases p28650_3 (m.d 0 4) (by simp) with h28672 | h28672
                                  · linarith only [h19744, h28672, hlam]
                                  · linarith only [h2, h28672, hlam]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h1, h23338, h28552, h28559, h28560, hlam, p28650_2]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h1, h23338, h28552, h28557, h28560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h23337, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28552, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28557, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28560, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h0, h19744, h28557, h28559, hc12, hc23, hlam, hphi, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28548, h28557, h28559, hc12, hc23, hlam, hphi, p28650_1]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [h28559, hlam, p28650_0]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  rcases p28650_3 (m.d 0 4) (by simp) with h28686 | h28686
                                  · linarith only [h28544, h28686, hlam]
                                  · linarith only [h23337, h28686, hlam]
                                · have p28650_0 := h28650c.1
                                  have p28650_1 := h28650c.2.1
                                  have p28650_2 := h28650c.2.2.1
                                  have p28650_3 := h28650c.2.2.2
                                  linarith only [hlam, p28650_0]
                              · linarith only [h28649, hlam, p28600_0]
                            · linarith only [h19744, h28648, hlam]
                          · linarith only [h28647, h4, hlam]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      rcases p28600_3 (m.d 0 2) (by simp) with h28693 | h28693
                      · linarith only [h22010, h28693, hlam]
                      · linarith only [h0, h28693, hlam]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28558, hlam, p28600_0]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [h28559, hlam, p28600_1]
                    · have p28600_0 := h28600c.1
                      have p28600_1 := h28600c.2.1
                      have p28600_2 := h28600c.2.2.1
                      have p28600_3 := h28600c.2.2.2
                      linarith only [hlam, p28600_0]
                  · rcases h2bigk with h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c | h28699c
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h4, hc12, hc23, hlam, hphi, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h4, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h19744, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h22010, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h0, hlam, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28546, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28548, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28550, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28710 | h28710
                      · linarith only [h28710, hlam, p28699_0]
                      · rcases p28699_3 (m.d 1 2) (by simp) with h28712 | h28712
                        · linarith only [h28546, h28712, hlam]
                        · rcases p28699_3 (m.d 2 3) (by simp) with h28714 | h28714
                          · rcases p28699_3 (m.d 2 4) (by simp) with h28715 | h28715
                            · linarith only [h28557, h28715, hlam]
                            · linarith only [h19744, h28715, hlam]
                          · linarith only [h28714, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28719 | h28719
                      · linarith only [h28719, h4, hlam]
                      · linarith only [h0, h28719, hlam]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28725 | h28725
                      · linarith only [h28725, hlam, p28699_0]
                      · rcases p28699_3 (m.d 1 2) (by simp) with h28727 | h28727
                        · linarith only [h28548, h28727, hlam]
                        · rcases p28699_3 (m.d 2 3) (by simp) with h28729 | h28729
                          · rcases p28699_3 (m.d 2 4) (by simp) with h28730 | h28730
                            · rcases p28699_3 (m.d 2 5) (by simp) with h28731 | h28731
                              · linarith only [h28559, h28731, hlam]
                              · linarith only [h22010, h28731, hlam]
                            · linarith only [h28730, hlam, p28699_0]
                          · linarith only [h28729, h4, hlam]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28736 | h28736
                      · linarith only [h19744, h28736, hlam]
                      · linarith only [h0, h28736, hlam]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28557, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h1, h23338, h28552, h28559, h28560, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28742 | h28742
                      · linarith only [h28742, hlam, p28699_0]
                      · rcases p28699_3 (m.d 1 2) (by simp) with h28744 | h28744
                        · linarith only [h28550, h28744, hlam]
                        · rcases p28699_3 (m.d 2 3) (by simp) with h28746 | h28746
                          · rcases p28699_3 (m.d 2 4) (by simp) with h28747 | h28747
                            · rcases p28699_3 (m.d 2 5) (by simp) with h28748 | h28748
                              · rcases h4bigk with h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c | h28749c
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h23337, h23338, h28548, hc12, hc35, hlam, hphi, ht23, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h19744, hlam, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28544, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h2, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28548, hlam, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h2, h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28555, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  rcases p28749_3 (m.d 0 4) (by simp) with h28760 | h28760
                                  · linarith only [h19744, h28760, hlam]
                                  · rcases p28749_3 (m.d 1 4) (by simp) with h28762 | h28762
                                    · linarith only [h28548, h28762, hlam]
                                    · rcases p28749_3 (m.d 2 4) (by simp) with h28764 | h28764
                                      · rcases p28749_3 (m.d 3 4) (by simp) with h28765 | h28765
                                        · linarith only [h28557, h28765, hlam]
                                        · rcases p28749_3 (m.d 4 5) (by simp) with h28767 | h28767
                                          · linarith only [h28559, h28767, hlam]
                                          · linarith only [h28544, h28767, hlam]
                                      · linarith only [h19744, h28764, hlam]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  rcases p28749_3 (m.d 0 4) (by simp) with h28771 | h28771
                                  · linarith only [h19744, h28771, hlam]
                                  · linarith only [h2, h28771, hlam]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h1, h23338, h28552, h28559, h28560, hlam, p28749_2]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h1, h23338, h28552, h28557, h28560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h23337, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28552, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28557, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28560, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h0, h19744, h28557, h28559, hc12, hc23, hlam, hphi, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28548, h28557, h28559, hc12, hc23, hlam, hphi, p28749_1]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [h28559, hlam, p28749_0]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  rcases p28749_3 (m.d 0 4) (by simp) with h28785 | h28785
                                  · linarith only [h28544, h28785, hlam]
                                  · linarith only [h23337, h28785, hlam]
                                · have p28749_0 := h28749c.1
                                  have p28749_1 := h28749c.2.1
                                  have p28749_2 := h28749c.2.2.1
                                  have p28749_3 := h28749c.2.2.2
                                  linarith only [hlam, p28749_0]
                              · linarith only [h28748, hlam, p28699_0]
                            · linarith only [h19744, h28747, hlam]
                          · linarith only [h28746, h4, hlam]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      rcases p28699_3 (m.d 0 2) (by simp) with h28792 | h28792
                      · linarith only [h22010, h28792, hlam]
                      · linarith only [h0, h28792, hlam]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28558, hlam, p28699_0]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [h28559, hlam, p28699_1]
                    · have p28699_0 := h28699c.1
                      have p28699_1 := h28699c.2.1
                      have p28699_2 := h28699c.2.2.1
                      have p28699_3 := h28699c.2.2.2
                      linarith only [hlam, p28699_0]
                  · rcases h2bigk with h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c | h28798c
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h4, hc12, hc23, hlam, hphi, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h4, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h19744, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h22010, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h0, hlam, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28546, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28548, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28550, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28809 | h28809
                      · linarith only [h28809, hlam, p28798_0]
                      · rcases p28798_3 (m.d 1 2) (by simp) with h28811 | h28811
                        · linarith only [h28546, h28811, hlam]
                        · rcases p28798_3 (m.d 2 3) (by simp) with h28813 | h28813
                          · rcases p28798_3 (m.d 2 4) (by simp) with h28814 | h28814
                            · linarith only [h28557, h28814, hlam]
                            · linarith only [h19744, h28814, hlam]
                          · linarith only [h28813, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28818 | h28818
                      · linarith only [h28818, h4, hlam]
                      · linarith only [h0, h28818, hlam]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28824 | h28824
                      · linarith only [h28824, hlam, p28798_0]
                      · rcases p28798_3 (m.d 1 2) (by simp) with h28826 | h28826
                        · linarith only [h28548, h28826, hlam]
                        · rcases p28798_3 (m.d 2 3) (by simp) with h28828 | h28828
                          · rcases p28798_3 (m.d 2 4) (by simp) with h28829 | h28829
                            · rcases p28798_3 (m.d 2 5) (by simp) with h28830 | h28830
                              · linarith only [h28559, h28830, hlam]
                              · linarith only [h22010, h28830, hlam]
                            · linarith only [h28829, hlam, p28798_0]
                          · linarith only [h28828, h4, hlam]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28835 | h28835
                      · linarith only [h19744, h28835, hlam]
                      · linarith only [h0, h28835, hlam]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28557, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h1, h23338, h28552, h28559, h28560, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28841 | h28841
                      · linarith only [h28841, hlam, p28798_0]
                      · rcases p28798_3 (m.d 1 2) (by simp) with h28843 | h28843
                        · linarith only [h28550, h28843, hlam]
                        · rcases p28798_3 (m.d 2 3) (by simp) with h28845 | h28845
                          · rcases p28798_3 (m.d 2 4) (by simp) with h28846 | h28846
                            · rcases p28798_3 (m.d 2 5) (by simp) with h28847 | h28847
                              · rcases h4bigk with h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c | h28848c
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h23337, h23338, h28548, hc12, hc35, hlam, hphi, ht23, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h19744, hlam, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28544, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h2, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28548, hlam, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h2, h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28555, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  rcases p28848_3 (m.d 0 4) (by simp) with h28859 | h28859
                                  · linarith only [h19744, h28859, hlam]
                                  · rcases p28848_3 (m.d 1 4) (by simp) with h28861 | h28861
                                    · linarith only [h28548, h28861, hlam]
                                    · rcases p28848_3 (m.d 2 4) (by simp) with h28863 | h28863
                                      · rcases p28848_3 (m.d 3 4) (by simp) with h28864 | h28864
                                        · linarith only [h28557, h28864, hlam]
                                        · rcases p28848_3 (m.d 4 5) (by simp) with h28866 | h28866
                                          · linarith only [h28559, h28866, hlam]
                                          · linarith only [h28544, h28866, hlam]
                                      · linarith only [h19744, h28863, hlam]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  rcases p28848_3 (m.d 0 4) (by simp) with h28870 | h28870
                                  · linarith only [h19744, h28870, hlam]
                                  · linarith only [h2, h28870, hlam]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h1, h23338, h28552, h28559, h28560, hlam, p28848_2]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h1, h23338, h28552, h28557, h28560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h23337, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28552, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28557, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28560, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h0, h19744, h28557, h28559, hc12, hc23, hlam, hphi, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28548, h28557, h28559, hc12, hc23, hlam, hphi, p28848_1]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [h28559, hlam, p28848_0]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  rcases p28848_3 (m.d 0 4) (by simp) with h28884 | h28884
                                  · linarith only [h28544, h28884, hlam]
                                  · linarith only [h23337, h28884, hlam]
                                · have p28848_0 := h28848c.1
                                  have p28848_1 := h28848c.2.1
                                  have p28848_2 := h28848c.2.2.1
                                  have p28848_3 := h28848c.2.2.2
                                  linarith only [hlam, p28848_0]
                              · linarith only [h28847, hlam, p28798_0]
                            · linarith only [h19744, h28846, hlam]
                          · linarith only [h28845, h4, hlam]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      rcases p28798_3 (m.d 0 2) (by simp) with h28891 | h28891
                      · linarith only [h22010, h28891, hlam]
                      · linarith only [h0, h28891, hlam]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28558, hlam, p28798_0]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [h28559, hlam, p28798_1]
                    · have p28798_0 := h28798c.1
                      have p28798_1 := h28798c.2.1
                      have p28798_2 := h28798c.2.2.1
                      have p28798_3 := h28798c.2.2.2
                      linarith only [hlam, p28798_0]
                  · rcases h2bigk with h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c | h28897c
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h4, hc12, hc23, hlam, hphi, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h4, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h19744, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h22010, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h0, hlam, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28546, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28548, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28550, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28908 | h28908
                      · linarith only [h28908, hlam, p28897_0]
                      · rcases p28897_3 (m.d 1 2) (by simp) with h28910 | h28910
                        · linarith only [h28546, h28910, hlam]
                        · rcases p28897_3 (m.d 2 3) (by simp) with h28912 | h28912
                          · rcases p28897_3 (m.d 2 4) (by simp) with h28913 | h28913
                            · linarith only [h28557, h28913, hlam]
                            · linarith only [h19744, h28913, hlam]
                          · linarith only [h28912, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28917 | h28917
                      · linarith only [h28917, h4, hlam]
                      · linarith only [h0, h28917, hlam]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28923 | h28923
                      · linarith only [h28923, hlam, p28897_0]
                      · rcases p28897_3 (m.d 1 2) (by simp) with h28925 | h28925
                        · linarith only [h28548, h28925, hlam]
                        · rcases p28897_3 (m.d 2 3) (by simp) with h28927 | h28927
                          · rcases p28897_3 (m.d 2 4) (by simp) with h28928 | h28928
                            · rcases p28897_3 (m.d 2 5) (by simp) with h28929 | h28929
                              · linarith only [h28559, h28929, hlam]
                              · linarith only [h22010, h28929, hlam]
                            · linarith only [h28928, hlam, p28897_0]
                          · linarith only [h28927, h4, hlam]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28934 | h28934
                      · linarith only [h19744, h28934, hlam]
                      · linarith only [h0, h28934, hlam]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28557, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h1, h23338, h28552, h28559, h28560, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28940 | h28940
                      · linarith only [h28940, hlam, p28897_0]
                      · rcases p28897_3 (m.d 1 2) (by simp) with h28942 | h28942
                        · linarith only [h28550, h28942, hlam]
                        · rcases p28897_3 (m.d 2 3) (by simp) with h28944 | h28944
                          · rcases p28897_3 (m.d 2 4) (by simp) with h28945 | h28945
                            · rcases p28897_3 (m.d 2 5) (by simp) with h28946 | h28946
                              · rcases h4bigk with h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c | h28947c
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h23337, h23338, h28548, hc12, hc35, hlam, hphi, ht23, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h19744, hlam, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28544, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h2, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28548, hlam, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h2, h23337, h23338, h28560, hc34, hc45, hlam, hphi, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28555, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  rcases p28947_3 (m.d 0 4) (by simp) with h28958 | h28958
                                  · linarith only [h19744, h28958, hlam]
                                  · rcases p28947_3 (m.d 1 4) (by simp) with h28960 | h28960
                                    · linarith only [h28548, h28960, hlam]
                                    · rcases p28947_3 (m.d 2 4) (by simp) with h28962 | h28962
                                      · rcases p28947_3 (m.d 3 4) (by simp) with h28963 | h28963
                                        · linarith only [h28557, h28963, hlam]
                                        · rcases p28947_3 (m.d 4 5) (by simp) with h28965 | h28965
                                          · linarith only [h28559, h28965, hlam]
                                          · linarith only [h28544, h28965, hlam]
                                      · linarith only [h19744, h28962, hlam]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  rcases p28947_3 (m.d 0 4) (by simp) with h28969 | h28969
                                  · linarith only [h19744, h28969, hlam]
                                  · linarith only [h2, h28969, hlam]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h1, h23338, h28552, h28559, h28560, hlam, p28947_2]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h1, h23338, h28552, h28557, h28560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h23337, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28552, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28557, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28560, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h0, h19744, h28557, h28559, hc12, hc23, hlam, hphi, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28548, h28557, h28559, hc12, hc23, hlam, hphi, p28947_1]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [h28559, hlam, p28947_0]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  rcases p28947_3 (m.d 0 4) (by simp) with h28983 | h28983
                                  · linarith only [h28544, h28983, hlam]
                                  · linarith only [h23337, h28983, hlam]
                                · have p28947_0 := h28947c.1
                                  have p28947_1 := h28947c.2.1
                                  have p28947_2 := h28947c.2.2.1
                                  have p28947_3 := h28947c.2.2.2
                                  linarith only [hlam, p28947_0]
                              · linarith only [h28946, hlam, p28897_0]
                            · linarith only [h19744, h28945, hlam]
                          · linarith only [h28944, h4, hlam]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      rcases p28897_3 (m.d 0 2) (by simp) with h28990 | h28990
                      · linarith only [h22010, h28990, hlam]
                      · linarith only [h0, h28990, hlam]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28558, hlam, p28897_0]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [h28559, hlam, p28897_1]
                    · have p28897_0 := h28897c.1
                      have p28897_1 := h28897c.2.1
                      have p28897_2 := h28897c.2.2.1
                      have p28897_3 := h28897c.2.2.2
                      linarith only [hlam, p28897_0]
        · linarith only [h28589, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h0, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28546, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28548, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28550, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h1, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h1, h23338, hc12, hc35, hlam, hphi, ht23, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h1, h23338, h28544, h28548, h28557, h28559, hc12, hc23, hlam, hphi, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28553, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h2, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h2, h23337, h23338, h28544, h28557, h28559, hc12, hc23, hlam, hphi, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28552, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28555, hlam, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h3, hlam, p28562_0]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28544, h28557, h28559, h3, hc12, hc23, hlam, hphi, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28544, h28546, h28557, h28559, h3, hc12, hc23, hlam, hphi, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [h28544, h28548, h28557, h28559, h3, hc12, hc23, hlam, hphi, p28562_1]
      · have p28562_0 := h28562c.1
        have p28562_1 := h28562c.2.1
        have p28562_2 := h28562c.2.2.1
        have p28562_3 := h28562c.2.2.2
        linarith only [hlam, p28562_0]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h29017 | h29017
    · linarith only [h1, h28552, h28559, h29017, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases h1bigk with h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c | h29019c
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        rcases p29019_3 (m.d 0 1) (by simp) with h29021 | h29021
        · rcases p29019_3 (m.d 1 2) (by simp) with h29022 | h29022
          · linarith only [h29022, hlam, p29019_0]
          · rcases p29019_3 (m.d 1 3) (by simp) with h29024 | h29024
            · linarith only [h1, h29024, hlam]
            · linarith only [h28546, h29024, hlam]
        · linarith only [h29021, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        rcases p29019_3 (m.d 0 1) (by simp) with h29028 | h29028
        · rcases p29019_3 (m.d 1 2) (by simp) with h29029 | h29029
          · linarith only [h0, h29029, hlam]
          · rcases p29019_3 (m.d 1 3) (by simp) with h29031 | h29031
            · linarith only [h29031, hlam, p29019_0]
            · rcases p29019_3 (m.d 1 4) (by simp) with h29033 | h29033
              · linarith only [h2, h29033, hlam]
              · rcases p29019_3 (m.d 1 5) (by simp) with h29035 | h29035
                · linarith only [h29035, h3, hlam]
                · linarith only [h28553, h29035, hlam]
        · linarith only [h29028, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        rcases p29019_3 (m.d 0 1) (by simp) with h29039 | h29039
        · rcases p29019_3 (m.d 1 2) (by simp) with h29040 | h29040
          · linarith only [h0, h29040, hlam]
          · rcases p29019_3 (m.d 1 3) (by simp) with h29042 | h29042
            · linarith only [h1, h29042, hlam]
            · linarith only [h28552, h29042, hlam]
        · linarith only [h29039, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        rcases p29019_3 (m.d 0 1) (by simp) with h29046 | h29046
        · rcases p29019_3 (m.d 1 2) (by simp) with h29047 | h29047
          · linarith only [h0, h29047, hlam]
          · rcases p29019_3 (m.d 1 3) (by simp) with h29049 | h29049
            · linarith only [h1, h29049, hlam]
            · rcases p29019_3 (m.d 1 4) (by simp) with h29051 | h29051
              · linarith only [h2, h29051, hlam]
              · rcases p29019_3 (m.d 1 5) (by simp) with h29053 | h29053
                · linarith only [h29053, hlam, p29019_0]
                · rcases h1emax with h29055 | h29055 | h29055 | h29055 | h29055
                  · linarith only [h29055, hc15, hlam, hphi, ht01, ht0b, ht5b, p29019_1]
                  · rcases h2bigk with h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c | h29057c
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h19744, hc12, hc24, hlam, hphi, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h4, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h19744, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h22010, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h0, hlam, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28546, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28548, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28550, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      rcases p29057_3 (m.d 0 2) (by simp) with h29068 | h29068
                      · linarith only [h29068, hlam, p29057_0]
                      · rcases p29057_3 (m.d 1 2) (by simp) with h29070 | h29070
                        · linarith only [h28546, h29070, hlam]
                        · rcases p29057_3 (m.d 2 3) (by simp) with h29072 | h29072
                          · rcases p29057_3 (m.d 2 4) (by simp) with h29073 | h29073
                            · linarith only [h28557, h29073, hlam]
                            · linarith only [h19744, h29073, hlam]
                          · linarith only [h29072, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      rcases p29057_3 (m.d 0 2) (by simp) with h29077 | h29077
                      · linarith only [h29077, h4, hlam]
                      · linarith only [h0, h29077, hlam]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h1, h23338, h28552, h28558, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h0, h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28557, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28559, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      rcases p29057_3 (m.d 0 2) (by simp) with h29088 | h29088
                      · linarith only [h29088, hlam, p29057_0]
                      · rcases p29057_3 (m.d 1 2) (by simp) with h29090 | h29090
                        · linarith only [h28550, h29090, hlam]
                        · rcases p29057_3 (m.d 2 3) (by simp) with h29092 | h29092
                          · rcases p29057_3 (m.d 2 4) (by simp) with h29093 | h29093
                            · linarith only [h28559, h29093, hlam]
                            · linarith only [h19744, h29093, hlam]
                          · linarith only [h29092, h4, hlam]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      rcases p29057_3 (m.d 0 2) (by simp) with h29097 | h29097
                      · linarith only [h22010, h29097, hlam]
                      · linarith only [h0, h29097, hlam]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h28558, hlam, p29057_0]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p29057_1]
                    · have p29057_0 := h29057c.1
                      have p29057_1 := h29057c.2.1
                      have p29057_2 := h29057c.2.2.1
                      have p29057_3 := h29057c.2.2.2
                      linarith only [hlam, p29057_0]
                  · rcases h2bigk with h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c | h29103c
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h19744, hc12, hc24, hlam, hphi, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h4, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h19744, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h22010, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h0, hlam, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28546, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28548, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28550, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      rcases p29103_3 (m.d 0 2) (by simp) with h29114 | h29114
                      · linarith only [h29114, hlam, p29103_0]
                      · rcases p29103_3 (m.d 1 2) (by simp) with h29116 | h29116
                        · linarith only [h28546, h29116, hlam]
                        · rcases p29103_3 (m.d 2 3) (by simp) with h29118 | h29118
                          · rcases p29103_3 (m.d 2 4) (by simp) with h29119 | h29119
                            · linarith only [h28557, h29119, hlam]
                            · linarith only [h19744, h29119, hlam]
                          · linarith only [h29118, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      rcases p29103_3 (m.d 0 2) (by simp) with h29123 | h29123
                      · linarith only [h29123, h4, hlam]
                      · linarith only [h0, h29123, hlam]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h0, h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28557, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28559, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      rcases p29103_3 (m.d 0 2) (by simp) with h29134 | h29134
                      · linarith only [h29134, hlam, p29103_0]
                      · rcases p29103_3 (m.d 1 2) (by simp) with h29136 | h29136
                        · linarith only [h28550, h29136, hlam]
                        · rcases p29103_3 (m.d 2 3) (by simp) with h29138 | h29138
                          · rcases p29103_3 (m.d 2 4) (by simp) with h29139 | h29139
                            · linarith only [h28559, h29139, hlam]
                            · linarith only [h19744, h29139, hlam]
                          · linarith only [h29138, h4, hlam]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      rcases p29103_3 (m.d 0 2) (by simp) with h29143 | h29143
                      · linarith only [h22010, h29143, hlam]
                      · linarith only [h0, h29143, hlam]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h28558, hlam, p29103_0]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p29103_1]
                    · have p29103_0 := h29103c.1
                      have p29103_1 := h29103c.2.1
                      have p29103_2 := h29103c.2.2.1
                      have p29103_3 := h29103c.2.2.2
                      linarith only [hlam, p29103_0]
                  · rcases h2bigk with h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c | h29149c
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h19744, hc12, hc24, hlam, hphi, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h4, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h19744, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h22010, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h0, hlam, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28546, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28548, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28550, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      rcases p29149_3 (m.d 0 2) (by simp) with h29160 | h29160
                      · linarith only [h29160, hlam, p29149_0]
                      · rcases p29149_3 (m.d 1 2) (by simp) with h29162 | h29162
                        · linarith only [h28546, h29162, hlam]
                        · rcases p29149_3 (m.d 2 3) (by simp) with h29164 | h29164
                          · rcases p29149_3 (m.d 2 4) (by simp) with h29165 | h29165
                            · linarith only [h28557, h29165, hlam]
                            · linarith only [h19744, h29165, hlam]
                          · linarith only [h29164, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      rcases p29149_3 (m.d 0 2) (by simp) with h29169 | h29169
                      · linarith only [h29169, h4, hlam]
                      · linarith only [h0, h29169, hlam]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h0, h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28557, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28559, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      rcases p29149_3 (m.d 0 2) (by simp) with h29180 | h29180
                      · linarith only [h29180, hlam, p29149_0]
                      · rcases p29149_3 (m.d 1 2) (by simp) with h29182 | h29182
                        · linarith only [h28550, h29182, hlam]
                        · rcases p29149_3 (m.d 2 3) (by simp) with h29184 | h29184
                          · rcases p29149_3 (m.d 2 4) (by simp) with h29185 | h29185
                            · linarith only [h28559, h29185, hlam]
                            · linarith only [h19744, h29185, hlam]
                          · linarith only [h29184, h4, hlam]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      rcases p29149_3 (m.d 0 2) (by simp) with h29189 | h29189
                      · linarith only [h22010, h29189, hlam]
                      · linarith only [h0, h29189, hlam]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h28558, hlam, p29149_0]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p29149_1]
                    · have p29149_0 := h29149c.1
                      have p29149_1 := h29149c.2.1
                      have p29149_2 := h29149c.2.2.1
                      have p29149_3 := h29149c.2.2.2
                      linarith only [hlam, p29149_0]
                  · rcases h2bigk with h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c | h29195c
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h19744, hc12, hc24, hlam, hphi, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h4, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h19744, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h22010, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h0, hlam, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28546, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28548, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28550, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      rcases p29195_3 (m.d 0 2) (by simp) with h29206 | h29206
                      · linarith only [h29206, hlam, p29195_0]
                      · rcases p29195_3 (m.d 1 2) (by simp) with h29208 | h29208
                        · linarith only [h28546, h29208, hlam]
                        · rcases p29195_3 (m.d 2 3) (by simp) with h29210 | h29210
                          · rcases p29195_3 (m.d 2 4) (by simp) with h29211 | h29211
                            · linarith only [h28557, h29211, hlam]
                            · linarith only [h19744, h29211, hlam]
                          · linarith only [h29210, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      rcases p29195_3 (m.d 0 2) (by simp) with h29215 | h29215
                      · linarith only [h29215, h4, hlam]
                      · linarith only [h0, h29215, hlam]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h19744, hc02, hc23, hlam, hphi, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h0, h22010, hc12, hc23, hlam, hphi, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h0, h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28559, hc12, hc45, hlam, hphi, ht23, ht34, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28557, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28559, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      rcases p29195_3 (m.d 0 2) (by simp) with h29226 | h29226
                      · linarith only [h29226, hlam, p29195_0]
                      · rcases p29195_3 (m.d 1 2) (by simp) with h29228 | h29228
                        · linarith only [h28550, h29228, hlam]
                        · rcases p29195_3 (m.d 2 3) (by simp) with h29230 | h29230
                          · rcases p29195_3 (m.d 2 4) (by simp) with h29231 | h29231
                            · linarith only [h28559, h29231, hlam]
                            · linarith only [h19744, h29231, hlam]
                          · linarith only [h29230, h4, hlam]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      rcases p29195_3 (m.d 0 2) (by simp) with h29235 | h29235
                      · linarith only [h22010, h29235, hlam]
                      · linarith only [h0, h29235, hlam]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h28558, hlam, p29195_0]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [h0, h19744, hc12, hc25, hlam, hphi, p29195_1]
                    · have p29195_0 := h29195c.1
                      have p29195_1 := h29195c.2.1
                      have p29195_2 := h29195c.2.2.1
                      have p29195_3 := h29195c.2.2.2
                      linarith only [hlam, p29195_0]
        · linarith only [h29046, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h0, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28546, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28548, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28550, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h1, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h1, h23338, hc12, hc35, hlam, hphi, ht23, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h1, h23338, h28548, hc12, hc35, hlam, hphi, ht23, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28553, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h2, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h2, h23337, h23338, hc12, hc35, hlam, hphi, ht23, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28552, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h28555, hlam, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h3, hlam, p29019_0]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h23338, h28558, h3, hc12, hc23, hlam, hphi, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h23338, h28546, h28558, h3, hc12, hc23, hlam, hphi, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [h23338, h28548, h28558, h3, hc12, hc23, hlam, hphi, p29019_1]
      · have p29019_0 := h29019c.1
        have p29019_1 := h29019c.2.1
        have p29019_2 := h29019c.2.2.1
        have p29019_3 := h29019c.2.2.2
        linarith only [hlam, p29019_0]

end R2N4
