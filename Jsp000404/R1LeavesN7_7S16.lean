import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19294000 in
set_option maxHeartbeats 19294000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s3 m hb1 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h9527 | h9527
    · rcases m.htr 0 2 4 (by decide) (by decide) with h9528 | h9528
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9529 | h9529
        · linarith only [h0, h3, h9529, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9531 | h9531
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9532 | h9532
            · linarith only [h1, h3, h9532, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9534 | h9534
              · linarith only [h0, h3, h9527, h9531, h9534, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9536 | h9536
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9537 | h9537
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9538 | h9538
                    · linarith only [h0, h3, h9527, h9529, h9531, h9538, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9540 | h9540
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9541 | h9541
                        · linarith only [h1, h3, h9538, h9541, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h3, h9536, h9541, hc23, hc35, hlam, hphi]
                      · linarith only [h9531, h9532, h9540, hc13, hc35, hlam, hphi]
                  · linarith only [h9528, h9529, h9537, hc12, hc25, hlam, hphi]
                · linarith only [h9527, h9529, h9536, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9547 | h9547
            · linarith only [h0, h3, h9528, h9531, h9547, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9549 | h9549
              · linarith only [h0, h3, h9528, h9549, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9551 | h9551
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9552 | h9552
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9553 | h9553
                    · linarith only [h0, h3, h9529, h9553, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9555 | h9555
                      · linarith only [h1, h3, h9531, h9553, h9555, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9557 | h9557
                        · linarith only [h1, h3, h9547, h9553, h9557, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · linarith only [h0, h3, h9551, h9557, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h9528, h9551, h9552, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h9527, h9529, h9551, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9562 | h9562
        · linarith only [h0, h3, h9562, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9564 | h9564
          · linarith only [h9527, h9528, h9564, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9566 | h9566
            · linarith only [h0, h3, h9527, h9566, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9568 | h9568
              · linarith only [h2, h3, h9568, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9570 | h9570
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9571 | h9571
                  · linarith only [h0, h9528, h9571, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9573 | h9573
                    · linarith only [h0, h3, h9573, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9575 | h9575
                      · linarith only [h1, h3, h9528, h9564, h9573, h9575, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9577 | h9577
                        · linarith only [h1, h3, h9573, h9577, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h2, h3, h9570, h9571, h9577, hc23, hc35, hlam, hphi]
                · linarith only [h9527, h9528, h9570, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h9581 | h9581
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9582 | h9582
        · linarith only [h1, h3, h9527, h9582, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9584 | h9584
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9585 | h9585
            · linarith only [h1, h3, h9585, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9587 | h9587
              · linarith only [h1, h3, h9527, h9581, h9587, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9589 | h9589
                · linarith only [h0, h3, h9527, h9581, h9589, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9591 | h9591
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9592 | h9592
                    · linarith only [h1, h3, h9582, h9589, h9592, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9594 | h9594
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9595 | h9595
                        · linarith only [h1, h3, h9585, h9595, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9597 | h9597
                          · linarith only [h1, h2, h3, h9527, h9581, h9587, h9589, h9597, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h3, h9589, h9591, h9597, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h9584, h9589, h9591, h9594, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h9527, h9581, h9585, h9591, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h9527, h9581, h9584, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h9603 | h9603
        · linarith only [h0, h3, h9603, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h9605 | h9605
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9606 | h9606
            · linarith only [h1, h3, h9606, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9608 | h9608
              · linarith only [h1, h3, h9605, h9608, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9610 | h9610
                · linarith only [h0, h9527, h9610, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9612 | h9612
                  · linarith only [h0, h9581, h9612, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9614 | h9614
                    · linarith only [h1, h3, h9603, h9610, h9614, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9616 | h9616
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9617 | h9617
                        · linarith only [h1, h3, h9606, h9614, h9617, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9619 | h9619
                          · linarith only [h1, h3, h9608, h9616, h9619, hlam]
                          · linarith only [h1, h3, h9616, h9619, hc34, hc45, hlam, hphi]
                      · linarith only [h9605, h9606, h9616, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h9623 | h9623
            · linarith only [h2, h3, h9605, h9623, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9625 | h9625
              · linarith only [h2, h3, h9625, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h9627 | h9627
                · linarith only [h0, h9527, h9627, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9629 | h9629
                  · linarith only [h1, h9581, h9605, h9627, h9629, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9631 | h9631
                    · linarith only [h0, h3, h9631, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h9633 | h9633
                      · linarith only [h1, h3, h9605, h9631, h9633, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h9635 | h9635
                        · linarith only [h1, h3, h9623, h9635, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h9637 | h9637
                          · linarith only [h2, h9625, h9637, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h9639 | h9639
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9640 | h9640
                              · linarith only [h2, h3, h9627, h9633, h9635, h9640, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h9527, h9605, h9639, h9640, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h9643 | h9643
                              · linarith only [h0, h9527, h9623, h9639, h9643, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h9645 | h9645
                                · linarith only [h2, h3, h9627, h9633, h9637, h9645, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h9647 | h9647
                                  · linarith only [h0, h9527, h9639, h9645, h9647, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h9527, h9639, h9647, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 19746000 in
set_option maxHeartbeats 19746000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s2 m hb1 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h9650 | h9650
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9651 | h9651
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9652 | h9652
        · linarith only [h0, h2, h9652, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9654 | h9654
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9655 | h9655
            · linarith only [h1, h2, h9655, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9657 | h9657
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9658 | h9658
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9659 | h9659
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9660 | h9660
                    · linarith only [h0, h9651, h9652, h9657, h9660, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9662 | h9662
                      · linarith only [h0, h2, h9660, h9662, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h9654, h9659, h9660, h9662, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h9651, h9652, h9659, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h9657, h9658, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9667 | h9667
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9668 | h9668
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9669 | h9669
                    · linarith only [h0, h9652, h9654, h9669, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9671 | h9671
                      · linarith only [h0, h2, h9669, h9671, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h9654, h9668, h9669, h9671, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h9651, h9652, h9668, hc12, hc24, hlam, hphi]
                · linarith only [h2, h9650, h9667, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9676 | h9676
            · linarith only [h1, h2, h9676, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9678 | h9678
              · linarith only [h9651, h9654, h9678, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9680 | h9680
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9681 | h9681
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9682 | h9682
                    · linarith only [h0, h9652, h9682, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9684 | h9684
                      · linarith only [h0, h2, h9654, h9682, h9684, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9686 | h9686
                        · linarith only [h1, h2, h9676, h9680, h9682, h9686, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h2, h9650, h9681, h9684, h9686, hc23, hc34, hlam, hphi]
                  · linarith only [h9651, h9654, h9681, hc12, hc25, hlam, hphi]
                · linarith only [h2, h9650, h9680, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9691 | h9691
        · linarith only [h0, h2, h9691, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9693 | h9693
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9694 | h9694
            · linarith only [h1, h2, h9694, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9696 | h9696
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9697 | h9697
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9698 | h9698
                  · linarith only [h9651, h9693, h9698, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9700 | h9700
                    · linarith only [h9691, h9693, h9700, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9702 | h9702
                      · linarith only [h1, h2, h9698, h9700, h9702, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h9693, h9700, h9702, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h9651, h9693, h9697, hlam]
              · linarith only [h9651, h9693, h9696, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9707 | h9707
            · linarith only [h1, h2, h9707, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9709 | h9709
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9710 | h9710
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9711 | h9711
                  · linarith only [h0, h9651, h9711, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9713 | h9713
                    · linarith only [h1, h2, h9691, h9711, h9713, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9715 | h9715
                      · linarith only [h0, h2, h9693, h9713, h9715, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9717 | h9717
                        · linarith only [h1, h2, h9707, h9713, h9717, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9719 | h9719
                          · linarith only [h1, h2, h9717, h9719, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h2, h9709, h9711, h9717, h9719, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h2, h9650, h9710, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9723 | h9723
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9724 | h9724
                  · linarith only [h0, h9651, h9724, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9726 | h9726
                    · linarith only [h0, h9691, h9726, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9728 | h9728
                      · linarith only [h0, h9693, h9728, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9730 | h9730
                        · linarith only [h1, h2, h9707, h9726, h9730, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9732 | h9732
                          · linarith only [h1, h2, h9709, h9732, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9734 | h9734
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9735 | h9735
                              · linarith only [h2, h9650, h9730, h9735, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9737 | h9737
                                · linarith only [h0, h9651, h9709, h9735, h9737, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9739 | h9739
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9740 | h9740
                                    · rcases h1bigk with h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c | h9741c
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, h9726, hc12, hc24, hlam, hphi, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, h9724, h9726, hc12, hc24, hlam, hphi, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, h9726, h9734, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p9741_1, u5ehi4]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h0, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9724, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9726, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9728, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h1, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h1, h2, h9726, hc12, hc24, hlam, hphi, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9730, hlam, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9732, hlam, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h0, h9726, hc12, hc24, hlam, hphi, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        rcases p9741_3 (m.d 0 1) (by simp) with h9758 | h9758
                                        · linarith only [h2, h9758, hlam]
                                        · linarith only [h0, h9758, hlam]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        rcases p9741_3 (m.d 0 1) (by simp) with h9761 | h9761
                                        · linarith only [h2, h9761, hlam]
                                        · linarith only [h1, h9761, hlam]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        rcases p9741_3 (m.d 0 1) (by simp) with h9765 | h9765
                                        · linarith only [h2, h9765, hlam]
                                        · linarith only [h9650, h9765, hlam]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9650, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, h9650, h9726, h9735, hc12, hc34, hlam, hphi, ht23, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h2, h9650, h9726, h9735, hc13, hc34, hlam, hphi, p9741_1]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [h9734, hlam, p9741_0]
                                      · have p9741_0 := h9741c.1
                                        have p9741_1 := h9741c.2.1
                                        have p9741_2 := h9741c.2.2.1
                                        have p9741_3 := h9741c.2.2.2
                                        linarith only [hlam, p9741_0]
                                    · linarith only [h2, h9650, h9726, h9735, h9740, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                                  · linarith only [h2, h9650, h9726, h9734, h9739, hlam]
                            · linarith only [h2, h9650, h9724, h9732, h9734, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h9650, h9723, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9777 | h9777
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9778 | h9778
        · linarith only [h0, h2, h9778, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9780 | h9780
          · linarith only [h0, h9650, h9780, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9782 | h9782
            · linarith only [h1, h2, h9782, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9784 | h9784
              · linarith only [h0, h9650, h9777, h9784, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9786 | h9786
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9787 | h9787
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9788 | h9788
                    · linarith only [h0, h2, h9778, h9788, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9790 | h9790
                      · linarith only [h0, h9650, h9780, h9790, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9792 | h9792
                        · linarith only [h1, h9650, h9782, h9786, h9792, hlam]
                        · linarith only [h0, h2, h9787, h9792, hc23, hc34, hlam, hphi]
                  · linarith only [h9777, h9778, h9787, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9796 | h9796
                  · linarith only [h0, h2, h9786, h9796, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h9777, h9786, h9796, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9799 | h9799
        · linarith only [h1, h2, h9777, h9799, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9801 | h9801
          · linarith only [h1, h9650, h9777, h9801, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9803 | h9803
            · linarith only [h1, h2, h9803, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9805 | h9805
              · linarith only [h1, h9650, h9805, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9807 | h9807
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9808 | h9808
                  · linarith only [h0, h9777, h9808, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9810 | h9810
                    · linarith only [h0, h9777, h9799, h9807, h9810, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9812 | h9812
                      · linarith only [h1, h9650, h9801, h9808, h9812, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9814 | h9814
                        · linarith only [h1, h9650, h9803, h9807, h9814, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9816 | h9816
                          · linarith only [h1, h9650, h9805, h9816, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9818 | h9818
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9819 | h9819
                              · linarith only [h1, h9650, h9808, h9814, h9818, h9819, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9821 | h9821
                                · linarith only [h1, h9650, h9808, h9816, h9819, h9821, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9823 | h9823
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9824 | h9824
                                    · rcases h1bigk with h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c | h9825c
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9650, h9810, h9818, hc12, hc24, hlam, hphi, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9650, h9808, h9810, h9818, hc12, hc24, hlam, hphi, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h2, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9650, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h0, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9808, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9810, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9812, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h1, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h1, h9650, h9810, h9818, hc12, hc24, hlam, hphi, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9814, hlam, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9816, hlam, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h0, h9810, hc12, hc24, hlam, hphi, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        rcases p9825_3 (m.d 0 1) (by simp) with h9842 | h9842
                                        · linarith only [h2, h9842, hlam]
                                        · linarith only [h0, h9842, hlam]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        rcases p9825_3 (m.d 0 1) (by simp) with h9845 | h9845
                                        · linarith only [h2, h9845, hlam]
                                        · linarith only [h1, h9845, hlam]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h1, h9650, h9808, h9810, h9819, hc12, hc34, hlam, hphi, ht23, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h1, h9808, h9812, hc12, hc25, hlam, hphi, p9825_1]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        rcases p9825_3 (m.d 0 1) (by simp) with h9851 | h9851
                                        · linarith only [h9650, h9851, hlam]
                                        · linarith only [h0, h9851, hlam]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        rcases p9825_3 (m.d 0 1) (by simp) with h9854 | h9854
                                        · linarith only [h9650, h9854, hlam]
                                        · linarith only [h1, h9854, hlam]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [h9818, hlam, p9825_0]
                                      · have p9825_0 := h9825c.1
                                        have p9825_1 := h9825c.2.1
                                        have p9825_2 := h9825c.2.2.1
                                        have p9825_3 := h9825c.2.2.2
                                        linarith only [hlam, p9825_0]
                                    · linarith only [h1, h2, h9807, h9808, h9810, h9819, h9824, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h2, h9807, h9810, h9823, hlam]
                            · linarith only [h2, h9807, h9818, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9862 | h9862
                  · linarith only [h0, h9777, h9862, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9864 | h9864
                    · linarith only [h0, h9799, h9864, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9866 | h9866
                      · linarith only [h1, h2, h9862, h9866, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9868 | h9868
                        · linarith only [h0, h1, h2, h9777, h9803, h9868, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9870 | h9870
                          · linarith only [h1, h2, h9870, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9872 | h9872
                            · linarith only [h1, h2, h9807, h9862, h9864, h9872, hc12, hc24, hlam, hphi]
                            · linarith only [h1, h2, h9862, h9872, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 20942000 in
set_option maxHeartbeats 20942000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s1 m hb1 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h9875 | h9875
    · rcases m.htr 0 1 5 (by decide) (by decide) with h9876 | h9876
      · rcases m.htr 0 2 3 (by decide) (by decide) with h9877 | h9877
        · linarith only [h0, h1, h9877, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h9879 | h9879
          · rcases m.htr 0 2 5 (by decide) (by decide) with h9880 | h9880
            · rcases m.htr 0 3 4 (by decide) (by decide) with h9881 | h9881
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9882 | h9882
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9883 | h9883
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9884 | h9884
                    · linarith only [h9877, h9879, h9883, h9884, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9886 | h9886
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9887 | h9887
                        · linarith only [h0, h1, h9887, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h0, h1, h9880, h9884, h9887, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h9879, h9884, h9886, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9891 | h9891
                    · linarith only [h0, h9877, h9891, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9893 | h9893
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9894 | h9894
                        · linarith only [h0, h1, h9891, h9894, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h9880, h9891, h9894, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h9879, h9891, h9893, hc12, hc23, hlam, hphi]
                · linarith only [h1, h9876, h9882, hlam]
              · linarith only [h1, h9875, h9881, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h9900 | h9900
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9901 | h9901
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9902 | h9902
                  · linarith only [h9879, h9880, h9902, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9904 | h9904
                    · linarith only [h0, h9877, h9879, h9904, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9906 | h9906
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9907 | h9907
                        · linarith only [h0, h1, h9880, h9901, h9904, h9907, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h9909 | h9909
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h9910 | h9910
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h9911 | h9911
                              · linarith only [h1, h9875, h9902, h9904, h9911, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h9913 | h9913
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h9914 | h9914
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9915 | h9915
                                    · linarith only [h9879, h9880, h9902, h9915, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9917 | h9917
                                      · linarith only [h9876, h9880, h9906, h9907, h9913, h9915, h9917, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c | h9919c
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h1, h9904, hc12, hc23, hlam, hphi, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h1, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          rcases p9919_3 (m.d 0 1) (by simp) with h9923 | h9923
                                          · rcases p9919_3 (m.d 1 2) (by simp) with h9924 | h9924
                                            · linarith only [h0, h9924, hlam]
                                            · linarith only [h9906, h9924, hlam]
                                          · linarith only [h9923, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h1, h9904, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9919_1, u5ehi1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h0, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9904, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h0, h9880, h9906, h9913, h9915, hc34, hc45, hlam, hphi, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9907, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h0, h9904, hc12, hc23, hlam, hphi, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          rcases p9919_3 (m.d 0 1) (by simp) with h9935 | h9935
                                          · linarith only [h1, h9935, hlam]
                                          · linarith only [h0, h9935, hlam]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          rcases p9919_3 (m.d 0 1) (by simp) with h9939 | h9939
                                          · linarith only [h1, h9939, hlam]
                                          · linarith only [h9875, h9939, hlam]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          rcases p9919_3 (m.d 0 1) (by simp) with h9942 | h9942
                                          · linarith only [h1, h9942, hlam]
                                          · linarith only [h9876, h9942, hlam]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9875, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9906, hlam, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9909, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9911, hlam, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9876, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9876, h9906, h9913, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h9910, hlam, p9919_0]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [h1, h9876, h9904, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9919_1]
                                        · have p9919_0 := h9919c.1
                                          have p9919_1 := h9919c.2.1
                                          have p9919_2 := h9919c.2.2.1
                                          have p9919_3 := h9919c.2.2.2
                                          linarith only [hlam, p9919_0]
                                  · linarith only [h1, h9876, h9904, h9914, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · linarith only [h1, h9876, h9904, h9906, h9907, h9913, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h9876, h9906, h9907, h9910, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h9876, h9906, h9907, h9909, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h9879, h9880, h9906, hc12, hc25, hlam, hphi]
                · linarith only [h1, h9876, h9901, hlam]
              · linarith only [h1, h9876, h9879, h9880, h9900, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h9962 | h9962
            · rcases m.htr 0 3 4 (by decide) (by decide) with h9963 | h9963
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9964 | h9964
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9965 | h9965
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9966 | h9966
                    · linarith only [h9877, h9962, h9966, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9968 | h9968
                      · linarith only [h0, h9879, h9962, h9968, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9970 | h9970
                        · linarith only [h1, h9875, h9966, h9968, h9970, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h9879, h9962, h9970, hc12, hc24, hlam, hphi]
                  · linarith only [h9879, h9962, h9965, hlam]
                · linarith only [h1, h9875, h9879, h9962, h9964, hlam]
              · linarith only [h1, h9875, h9963, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h9976 | h9976
              · rcases m.htr 0 3 5 (by decide) (by decide) with h9977 | h9977
                · rcases m.htr 0 4 5 (by decide) (by decide) with h9978 | h9978
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9979 | h9979
                    · linarith only [h0, h1, h9877, h9979, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9981 | h9981
                      · linarith only [h0, h9879, h9981, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9983 | h9983
                        · linarith only [h0, h1, h9962, h9979, h9983, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h9985 | h9985
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h9986 | h9986
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h9987 | h9987
                              · linarith only [h1, h9875, h9979, h9987, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h1, h9875, h9978, h9979, h9981, h9987, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h9986, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h9875, h9978, h9985, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9992 | h9992
                    · linarith only [h0, h9877, h9992, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h9994 | h9994
                      · linarith only [h0, h9879, h9994, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h9996 | h9996
                        · linarith only [h0, h1, h9962, h9992, h9996, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h9998 | h9998
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h9999 | h9999
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10000 | h10000
                              · linarith only [h1, h10000, h9875, h9992, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10002 | h10002
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10003 | h10003
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10004 | h10004
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10005 | h10005
                                      · linarith only [h1, h10000, h10005, h9876, h9879, h9978, h9998, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                      · rcases h1bigk with h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c | h10007c
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9992, hc12, hc23, hlam, hphi, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9992, h9994, hc12, hc23, hlam, hphi, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9992, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10007_1, u5ehi1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h0, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9992, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9994, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9996, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h0, h9992, hc12, hc23, hlam, hphi, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          rcases p10007_3 (m.d 0 1) (by simp) with h10019 | h10019
                                          · linarith only [h1, h10019, hlam]
                                          · linarith only [h0, h10019, hlam]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          rcases p10007_3 (m.d 0 1) (by simp) with h10023 | h10023
                                          · linarith only [h1, h10023, hlam]
                                          · linarith only [h10023, h9875, hlam]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          rcases p10007_3 (m.d 0 1) (by simp) with h10026 | h10026
                                          · linarith only [h1, h10026, hlam]
                                          · linarith only [h10026, h9876, hlam]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9875, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9875, h9992, hc12, hc23, hlam, hphi, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9998, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h10000, hlam, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9876, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9876, h9992, hc12, hc23, hlam, hphi, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h9999, hlam, p10007_0]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [h1, h9876, h9992, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10007_1]
                                        · have p10007_0 := h10007c.1
                                          have p10007_1 := h10007c.2.1
                                          have p10007_2 := h10007c.2.2.1
                                          have p10007_3 := h10007c.2.2.2
                                          linarith only [hlam, p10007_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10039 | h10039
                                      · linarith only [h10039, h9976, h9978, hlam]
                                      · rcases h1bigk with h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c | h10041c
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9992, hc12, hc23, hlam, hphi, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9992, h9994, hc12, hc23, hlam, hphi, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9992, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10041_1, u5ehi1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h0, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9992, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9994, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9996, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h0, h9992, hc12, hc23, hlam, hphi, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          rcases p10041_3 (m.d 0 1) (by simp) with h10053 | h10053
                                          · linarith only [h1, h10053, hlam]
                                          · linarith only [h0, h10053, hlam]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          rcases p10041_3 (m.d 0 1) (by simp) with h10057 | h10057
                                          · linarith only [h1, h10057, hlam]
                                          · linarith only [h10057, h9875, hlam]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          rcases p10041_3 (m.d 0 1) (by simp) with h10060 | h10060
                                          · linarith only [h1, h10060, hlam]
                                          · linarith only [h10060, h9876, hlam]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9875, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9875, h9992, hc12, hc23, hlam, hphi, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9998, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h10000, hlam, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9876, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9876, h9992, hc12, hc23, hlam, hphi, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h9999, hlam, p10041_0]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [h1, h9876, h9992, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10041_1]
                                        · have p10041_0 := h10041c.1
                                          have p10041_1 := h10041c.2.1
                                          have p10041_2 := h10041c.2.2.1
                                          have p10041_3 := h10041c.2.2.2
                                          linarith only [hlam, p10041_0]
                                  · linarith only [h1, h10003, h9876, h9992, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · linarith only [h1, h10002, h9876, h9992, h9999, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h1, h9876, h9999, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h9876, h9998, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h1, h9876, h9977, hlam]
              · linarith only [h1, h9875, h9976, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10079 | h10079
        · linarith only [h0, h1, h10079, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10081 | h10081
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10082 | h10082
            · linarith only [h0, h10082, h9876, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10084 | h10084
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10085 | h10085
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10086 | h10086
                  · linarith only [h0, h10081, h10086, h9876, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10088 | h10088
                    · linarith only [h0, h1, h10079, h10088, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10090 | h10090
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10091 | h10091
                        · linarith only [h0, h10082, h10091, h9876, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10093 | h10093
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10094 | h10094
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10095 | h10095
                              · linarith only [h10086, h10095, h9875, h9876, hlam]
                              · linarith only [h0, h10090, h10095, h9876, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h10085, h10090, h10094, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h10090, h10093, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h10079, h10081, h10090, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10101 | h10101
                  · linarith only [h0, h1, h10081, h10085, h10101, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10103 | h10103
                    · linarith only [h0, h1, h10085, h10103, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10105 | h10105
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10106 | h10106
                        · linarith only [h0, h1, h10085, h10106, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10108 | h10108
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10109 | h10109
                            · linarith only [h0, h1, h10085, h10105, h10109, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h1, h10105, h10109, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h10105, h10108, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h10079, h10081, h10105, hc12, hc23, hlam, hphi]
              · linarith only [h1, h10084, h9875, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10115 | h10115
            · linarith only [h10081, h10115, h9875, h9876, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10117 | h10117
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10118 | h10118
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10119 | h10119
                  · linarith only [h10119, h9875, h9876, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10121 | h10121
                    · linarith only [h0, h10079, h10121, h9876, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10123 | h10123
                      · linarith only [h0, h10081, h10123, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10125 | h10125
                        · linarith only [h0, h10115, h10125, h9876, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10127 | h10127
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10128 | h10128
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10129 | h10129
                              · linarith only [h10081, h10119, h10128, h10129, h9875, h9876, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10131 | h10131
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10132 | h10132
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10133 | h10133
                                    · linarith only [h0, h10129, h10131, h10133, h9876, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10135 | h10135
                                      · linarith only [h10127, h10128, h10133, h10135, h9875, h9876, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c | h10137c
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10125, h10133, h9876, hc12, hc45, hlam, hphi, ht23, ht34, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h1, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10125, h10133, h9876, hc14, hc45, hlam, hphi, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h9876, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h0, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10121, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10123, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10125, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h0, h10121, hc12, hc23, hlam, hphi, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          rcases p10137_3 (m.d 0 1) (by simp) with h10149 | h10149
                                          · linarith only [h1, h10149, hlam]
                                          · linarith only [h0, h10149, hlam]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          rcases p10137_3 (m.d 0 1) (by simp) with h10153 | h10153
                                          · linarith only [h1, h10153, hlam]
                                          · linarith only [h10153, h9875, hlam]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10121, h10123, h9875, h9876, hc12, hc23, hlam, hphi, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h9875, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h9875, h9876, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10127, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10129, hlam, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h0, h10125, h10133, hc12, hc45, hlam, hphi, ht23, ht34, p10137_1]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          rcases p10137_3 (m.d 0 1) (by simp) with h10163 | h10163
                                          · linarith only [h10163, h9876, hlam]
                                          · linarith only [h0, h10163, hlam]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [h10128, hlam, p10137_0]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          rcases p10137_3 (m.d 0 1) (by simp) with h10167 | h10167
                                          · linarith only [h10167, h9876, hlam]
                                          · linarith only [h10167, h9875, hlam]
                                        · have p10137_0 := h10137c.1
                                          have p10137_1 := h10137c.2.1
                                          have p10137_2 := h10137c.2.2.1
                                          have p10137_3 := h10137c.2.2.2
                                          linarith only [hlam, p10137_0]
                                  · linarith only [h1, h10118, h10121, h10132, h9875, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h10121, h10123, h10128, h10131, h9875, h9876, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h10118, h10128, hlam]
                          · linarith only [h1, h10123, h10127, h9875, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10175 | h10175
                  · linarith only [h1, h10118, h10175, h9875, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10177 | h10177
                    · linarith only [h0, h1, h10118, h10177, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10179 | h10179
                      · linarith only [h0, h10081, h10179, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10181 | h10181
                        · linarith only [h1, h10118, h10179, h10181, h9875, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10183 | h10183
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10184 | h10184
                            · linarith only [h1, h10118, h10177, h10179, h10184, h9875, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h10179, h10184, h9875, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h10179, h10183, h9875, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h10117, h9875, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h10189 | h10189
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10190 | h10190
        · linarith only [h0, h1, h10190, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10192 | h10192
          · linarith only [h0, h10192, h9875, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10194 | h10194
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10195 | h10195
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10196 | h10196
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10197 | h10197
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10198 | h10198
                    · linarith only [h10190, h10194, h10198, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10200 | h10200
                      · linarith only [h0, h10192, h10194, h10200, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10202 | h10202
                        · linarith only [h0, h1, h10198, h10202, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h10194, h10198, h10202, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h10194, h10197, h9875, hlam]
                · linarith only [h0, h1, h10194, h10196, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10207 | h10207
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10208 | h10208
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10209 | h10209
                    · linarith only [h0, h1, h10195, h10209, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10211 | h10211
                      · linarith only [h0, h1, h10192, h10195, h10211, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10213 | h10213
                        · linarith only [h0, h1, h10195, h10213, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1, h10194, h10195, h10213, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h10189, h10195, h10208, hlam]
                · linarith only [h0, h1, h10194, h10207, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10218 | h10218
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10219 | h10219
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10220 | h10220
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10221 | h10221
                    · linarith only [h0, h1, h10190, h10221, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10223 | h10223
                      · linarith only [h0, h1, h10192, h10221, h10223, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10225 | h10225
                        · linarith only [h0, h1, h10194, h10219, h10221, h10225, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10227 | h10227
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10228 | h10228
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10229 | h10229
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10230 | h10230
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10231 | h10231
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10232 | h10232
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10233 | h10233
                                      · rcases h1bigk with h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c | h10234c
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10221, h10227, h9875, hc12, hc23, hlam, hphi, p10234_1]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h1, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h9875, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10221, h10227, h9875, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10234_1, u5ehi1]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h0, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10221, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10223, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10225, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h0, h10221, hc12, hc23, hlam, hphi, p10234_1]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          rcases p10234_3 (m.d 0 1) (by simp) with h10246 | h10246
                                          · linarith only [h1, h10246, hlam]
                                          · linarith only [h0, h10246, hlam]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10189, h10221, h10228, h10233, h9875, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10234_1, u5ehi4]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          rcases p10234_3 (m.d 0 1) (by simp) with h10251 | h10251
                                          · linarith only [h1, h10251, hlam]
                                          · linarith only [h10189, h10251, hlam]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10189, h10228, h10233, hc14, hlam, hphi, ht01, ht0b, ht5b, p10234_1, u5ehi4]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          rcases p10234_3 (m.d 0 1) (by simp) with h10255 | h10255
                                          · linarith only [h10255, h9875, hlam]
                                          · linarith only [h0, h10255, hlam]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10227, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          rcases p10234_3 (m.d 0 1) (by simp) with h10260 | h10260
                                          · linarith only [h10260, h9875, hlam]
                                          · linarith only [h10189, h10260, hlam]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10189, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h1, h10189, h10221, hc12, hc23, hlam, hphi, p10234_1]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10228, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [h10229, hlam, p10234_0]
                                        · have p10234_0 := h10234c.1
                                          have p10234_1 := h10234c.2.1
                                          have p10234_2 := h10234c.2.2.1
                                          have p10234_3 := h10234c.2.2.2
                                          linarith only [hlam, p10234_0]
                                      · rcases h1bigk with h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c | h10268c
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10221, h10227, h9875, hc12, hc23, hlam, hphi, p10268_1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h1, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h9875, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10221, h10227, h9875, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10268_1, u5ehi1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h0, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10221, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10223, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10225, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h0, h10221, hc12, hc23, hlam, hphi, p10268_1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          rcases p10268_3 (m.d 0 1) (by simp) with h10280 | h10280
                                          · linarith only [h1, h10280, hlam]
                                          · linarith only [h0, h10280, hlam]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10189, h10221, h10229, h10233, h9875, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10268_1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          rcases p10268_3 (m.d 0 1) (by simp) with h10285 | h10285
                                          · linarith only [h1, h10285, hlam]
                                          · linarith only [h10189, h10285, hlam]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10189, h10229, h10233, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10268_1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          rcases p10268_3 (m.d 0 1) (by simp) with h10289 | h10289
                                          · linarith only [h10289, h9875, hlam]
                                          · linarith only [h0, h10289, hlam]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10227, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          rcases p10268_3 (m.d 0 1) (by simp) with h10294 | h10294
                                          · linarith only [h10294, h9875, hlam]
                                          · linarith only [h10189, h10294, hlam]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10189, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h1, h10189, h10221, hc12, hc23, hlam, hphi, p10268_1]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10228, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [h10229, hlam, p10268_0]
                                        · have p10268_0 := h10268c.1
                                          have p10268_1 := h10268c.2.1
                                          have p10268_2 := h10268c.2.2.1
                                          have p10268_3 := h10268c.2.2.2
                                          linarith only [hlam, p10268_0]
                                    · linarith only [h10189, h10223, h10232, h9875, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                                  · linarith only [h10189, h10223, h10228, h10230, h10231, h9875, hlam]
                                · linarith only [h10190, h10218, h10230, hlam]
                              · linarith only [h10189, h10228, h10229, h9875, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · linarith only [h10189, h10227, h10228, h9875, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h10189, h10218, h10227, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                  · linarith only [h10189, h10220, h9875, hlam]
                · linarith only [h1, h10189, h10219, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10310 | h10310
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10311 | h10311
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10312 | h10312
                    · linarith only [h0, h1, h10218, h10312, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10314 | h10314
                      · linarith only [h0, h10192, h10314, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10316 | h10316
                        · linarith only [h0, h1, h10218, h10316, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10318 | h10318
                          · linarith only [h1, h10189, h10218, h10318, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · linarith only [h1, h10189, h10318, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                  · linarith only [h1, h10189, h10218, h10311, hlam]
                · linarith only [h1, h10189, h10310, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h10323 | h10323
        · linarith only [h0, h1, h10323, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h10325 | h10325
          · linarith only [h0, h10325, h9875, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h10327 | h10327
            · linarith only [h0, h10189, h10327, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h10329 | h10329
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10330 | h10330
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10331 | h10331
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10332 | h10332
                    · linarith only [h0, h1, h10323, h10332, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10334 | h10334
                      · linarith only [h0, h1, h10325, h10331, h10334, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10336 | h10336
                        · linarith only [h0, h10189, h10327, h10336, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10338 | h10338
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10339 | h10339
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10340 | h10340
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h10341 | h10341
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h10342 | h10342
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h10343 | h10343
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10344 | h10344
                                      · rcases h1bigk with h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c | h10345c
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10189, h10332, h10338, h10340, hc12, hc23, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h1, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h9875, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10189, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10332, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10334, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10336, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10332, hc12, hc23, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          rcases p10345_3 (m.d 0 1) (by simp) with h10357 | h10357
                                          · linarith only [h1, h10357, hlam]
                                          · linarith only [h0, h10357, hlam]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10332, h9875, hc12, hc23, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10189, h10332, hc12, hc23, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10334, hc12, hc24, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          rcases p10345_3 (m.d 0 1) (by simp) with h10364 | h10364
                                          · linarith only [h10364, h9875, hlam]
                                          · linarith only [h0, h10364, hlam]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10338, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10189, h10332, h10338, hc12, hc23, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h0, h10336, hc12, hc25, hlam, hphi, p10345_1]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          rcases p10345_3 (m.d 0 1) (by simp) with h10371 | h10371
                                          · linarith only [h10189, h10371, hlam]
                                          · linarith only [h0, h10371, hlam]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10339, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [h10340, hlam, p10345_0]
                                        · have p10345_0 := h10345c.1
                                          have p10345_1 := h10345c.2.1
                                          have p10345_2 := h10345c.2.2.1
                                          have p10345_3 := h10345c.2.2.2
                                          linarith only [hlam, p10345_0]
                                      · rcases h1bigk with h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c | h10377c
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h1, h10332, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h1, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h9875, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10189, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10332, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10334, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10336, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10332, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          rcases p10377_3 (m.d 0 1) (by simp) with h10389 | h10389
                                          · linarith only [h1, h10389, hlam]
                                          · linarith only [h0, h10389, hlam]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10332, h9875, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10189, h10332, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10334, h10341, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          rcases p10377_3 (m.d 0 1) (by simp) with h10396 | h10396
                                          · linarith only [h10396, h9875, hlam]
                                          · linarith only [h0, h10396, hlam]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10338, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10189, h10334, h10341, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h0, h10336, h10341, h10343, hc12, hc23, hlam, hphi, p10377_1]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          rcases p10377_3 (m.d 0 1) (by simp) with h10403 | h10403
                                          · linarith only [h10189, h10403, hlam]
                                          · linarith only [h0, h10403, hlam]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10339, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [h10340, hlam, p10377_0]
                                        · have p10377_0 := h10377c.1
                                          have p10377_1 := h10377c.2.1
                                          have p10377_2 := h10377c.2.2.1
                                          have p10377_3 := h10377c.2.2.2
                                          linarith only [hlam, p10377_0]
                                    · linarith only [h0, h10329, h10331, h10334, h10343, h9875, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h10332, h10342, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h10189, h10332, h10338, h10340, h10341, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h10331, h10340, h9875, hlam]
                            · linarith only [h0, h1, h10339, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h10338, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10415 | h10415
                    · linarith only [h0, h1, h10323, h10415, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10417 | h10417
                      · linarith only [h0, h10331, h10417, h9875, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10419 | h10419
                        · linarith only [h0, h10331, h10419, h9875, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10421 | h10421
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10422 | h10422
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h10423 | h10423
                              · linarith only [h0, h10331, h10415, h10421, h10423, h9875, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h10423, h9875, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h10330, h10422, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h10421, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10428 | h10428
                  · linarith only [h10329, h10330, h10428, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10430 | h10430
                    · linarith only [h0, h1, h10330, h10430, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10432 | h10432
                      · linarith only [h0, h10428, h10432, h9875, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10434 | h10434
                        · linarith only [h0, h10329, h10330, h10434, h9875, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10436 | h10436
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h10437 | h10437
                            · linarith only [h0, h10329, h10330, h10430, h10437, h9875, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h10437, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h10329, h10436, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h10441 | h10441
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10442 | h10442
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10443 | h10443
                    · linarith only [h0, h10323, h10443, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10445 | h10445
                      · linarith only [h0, h10325, h10445, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10447 | h10447
                        · linarith only [h0, h10189, h10327, h10447, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10449 | h10449
                          · linarith only [h0, h10189, h10329, h10441, h10443, h10449, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h10449, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h10329, h10441, h10442, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h10453 | h10453
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10454 | h10454
                    · linarith only [h0, h1, h10441, h10454, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10456 | h10456
                      · linarith only [h0, h10325, h10456, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10458 | h10458
                        · linarith only [h0, h1, h10441, h10458, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10460 | h10460
                          · linarith only [h0, h1, h10329, h10454, h10460, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h10460, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h10463 | h10463
                    · linarith only [h0, h1, h10441, h10463, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10465 | h10465
                      · linarith only [h0, h1, h10325, h10329, h10465, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h10467 | h10467
                        · linarith only [h0, h1, h10329, h10453, h10467, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h10469 | h10469
                          · linarith only [h0, h1, h10329, h10463, h10469, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h10469, hc12, hc34, hlam, hphi, ht23]

end R2N4
