import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard107
open N4R2RowDataReplay

-- Original cycle 000f49d7e18f9d0c1459be9e5548a3825bed51e92546704874de034984a8adea; original global index 7.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 0074a946975d986f67fa5fb456c3d1523e6d2108dbc3de9282c026cba35c554e; original global index 41.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 00ff9bd768bc08955cde9d43907590ed073c2856da3f4f9fd6f6920faebde8e9; original global index 87.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 018e18a6f3004e2e1e8ebbbabcaac7e5eaf6aa621abd2c2e625cb4097c8b2319; original global index 131.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 033ca5ade7524fad3a443ae7c91f6e6a17d2f04df5360742b23f61e3e75159df; original global index 261.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 045177addd8632b6124533fe8877185d39e178582f6b5af61a0fece59458aad1; original global index 341.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0451dbd8f382534b6827c272d2fc88f718354ea99e7ce11223f4207ff7a46867; original global index 342.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 04a8b29bfacffc164bb6ef48dd19f24dff5b2966fc416ab8a0d016c2b0bb7475; original global index 371.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 04f8b2ef7aeda52659761a3e3ef3f4f26e6668c67c4b8374589259f90935c0ab; original global index 397.
def localCycle00008 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 3, .gapLower 6 3, .triangle 4 1]

-- Original cycle 0884e4b3d5b855c124601168ba0760506545428e5805162f078d00e78cca1df5; original global index 678.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 08b906b888f9b6cc51460d2688bb5a129de43bd384f324d3b9feffaf9b04eca4; original global index 698.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0a5066e1436ce017cd4c0bb0ffd7d1eb3383bcf3414db6f765a6a1ba59ac8a37; original global index 824.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0a9845994613410d2c7cd30d172a25ac7154b093ec09cfccad60daf6a694ecc4; original global index 845.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0bdcace659f3e5b5b1b37d21689afdac1c3fed9011ebce52388d37edb612a230; original global index 944.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 4, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 2 1, .triangle 3 0, .triangle 17 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 0ccdab088c5038e8d2a050b5a208a5b1fef9a7d1fef43940d22c7f387679cfbf; original global index 1014.
def localCycle00014 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 0ea29633a3a2fd0bba1905c215b049014d2ee17610df510cbf4a3481ef5f7ab7; original global index 1156.
def localCycle00015 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 29 1]

-- Original cycle 0ec4e83fd5ce31c7b25da4a69acf0cf5659e146e33aba5733d871def85e6e1d1; original global index 1168.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0eec5579bea59e2893bfc82af1f1d322d825d42661b73111be9028e9c32a1ede; original global index 1180.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .corridorLower 3 5]

-- Original cycle 0fb3acbab8b6775d37b9e34036e676f98dd537cd8c2783010ef57ee83e9ae79a; original global index 1252.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 10696321c1c42035f0547f1889f59275a7d8037225d6cc1873c9b172a189c3d9; original global index 1317.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 1 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 3, .triangle 4 1, .triangle 21 1, .triangle 33 1, .corridorLower 3 5]

-- Original cycle 124818382725b760c2148223e60c6e8f03a60a33f8d35f49811d38b5718bfdbb; original global index 1453.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 4 3, .gapUpper 3 3]

-- Original cycle 14241f7054c6cc30c9f867b68f307813803e663c55dc9eaf62821504581faddb; original global index 1592.
def localCycle00021 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 4, .gapLower 4 4, .gapLower 0 4]

-- Original cycle 1470097e5f8bbf03b6923e65f0c7ecc2d3e4f4721c97dea752c28a8aa7e0330a; original global index 1616.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 1511e00c9475d1ce0f888d4d8cbe6a7972aa265c1b2d3383a13bec9288623d25; original global index 1670.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 156b777143e47af89725913aaccc1759e20ee561de4259c78bbed3f3d93f30cb; original global index 1696.
def localCycle00024 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle 17321a73b14b68ad3d8cef4a0a58ee6b79e3182a2c5f06651216520e7c7efb7d; original global index 1826.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 183947ec3b167d01d332f14141b4910584484dc6f3097d3834936bd1e4cdbdd5; original global index 1894.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 19ff53973877481f11328bcd5f07feac01ed58bcce5f52e2ef66e89c460a31f4; original global index 2032.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 1a45a4a848e1537a8a2f3bcfd6ec3fd6e7fef581f9de9e1e9705cd27a5e36ae7; original global index 2053.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1a8566c3fbda71f3077258c866c190030e93a85aee0d11a84ce344790164cd49; original global index 2065.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 13 2, .gapLower 0 3, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1ae1b9b61a0dcd244f1f1845c90925d3efa0ea20ce0c981d0e6358c1cbe2f93f; original global index 2086.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1d5deda892d4e9d8a3759c93fdcde894c6d3b003e267d769e0c3e6df8a5051a0; original global index 2261.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 0 5, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .gapLower 0 4, .triangle 4 1, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1df19298527cf08919a7f51972b38c831ff18e732d31c4a8469ad92d3b5b105e; original global index 2301.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 14 0, .gapLower 0 1]

-- Original cycle 1ec566c065e6350e8e384b109c9b1149bf6630d75d04bcb389be00f6d33118ba; original global index 2362.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 3, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1eeaba8afba93cdda038ce114cae3cb4f425f5efe30a0ae9cfc2a12614d092e0; original global index 2374.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1fe6d9122f9c2bed17f9ae1adbb6c5450a18bd1a397b21b78c2e8df17c048c2c; original global index 2449.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 0 2, .triangle 8 0, .gapLower 6 3, .gapUpper 1 3]

-- Original cycle 212bd199acdb6baea1ff4792f536743fac0b4ed9dec9a0e7d04663aa9c0ae7e6; original global index 2542.
def localCycle00036 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 0 1]

-- Original cycle 22c551238c75cfff6ef46c0b386db68a3bc43ef8a18488ddc31263acf4e9764c; original global index 2663.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 24a1a18818f8a112e2f144160079e018837f7f7707c0b3adebd69845cfc7fe01; original global index 2809.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 2, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 24b6900874ed97277acb8aba90cf299d96676b5e058ff5172f0ea8740d48d777; original global index 2815.
def localCycle00039 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 8 2, .triangle 14 1]

-- Original cycle 25bd2dd4965d61bc586fd6b9c46412b10f1359c0a838e456f9e8afc7485721bc; original global index 2896.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 26a4dfc51539c312785d3578d15348bd24ead6b37d5a28cebb8601b39adb1791; original global index 2961.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 27389bfdcaf66abdacff5eecc6b78557ec9b309a9cc5639eda8ee7bf5c4f96f8; original global index 3002.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 27ab048c79b54a3d4464e55fc6a78d6f88e7b9cbbe97ca5850f9b5b694ad4237; original global index 3027.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 24 2, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 28532a945b62dea40d6bea015272ce1f62fd0635c16d13f3f1bb03ab7dbfb5a3; original global index 3092.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2958fb68c875ad3854699bdb4e1a014a9915ca8a8d6a576cf8d831eedce3f2b6; original global index 3155.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 2987fd91a816e5bf10507f29c982d2003dc5023598815027b17ad36f75c95fbb; original global index 3165.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 29cd56635599c8224ffa5591f70f7ed113f9dc1a5eac7c669726ca6c52915f12; original global index 3192.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2bfa91e9696235d60c578d266a60e397bbf50cc667f01c955c06c89c82831053; original global index 3363.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 2d080be512d8d23db6205a7cb89eb007ab01be83b366d58b74d77ac44af54038; original global index 3439.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2d6928c5406bec3c25cc9ca07282209b3844cfc2d41d69265bfdc7b880bb77e3; original global index 3463.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 21 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2d93a249c3fa5f4da873c523bc8835eb93e7b08016a980cef89f0c05a2c3c2d6; original global index 3471.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 2e0af3192814505be6cfeb7700d68fef27a18e5a4338b3ed21e0bd4232569116; original global index 3517.
def localCycle00052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 14 1]

-- Original cycle 2f5f1973638abf60a05ca9105fcdf43bbae87223819a3a559b85d6faa66bb2e9; original global index 3619.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 31227a96e7ef2138499af420945c448655cc883fd20650488793823b92802547; original global index 3748.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 3, .triangle 4 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 328c0575b38ce5100a5a327e7cd886a4e022468fc21b09dd1d76e18df0d6f68f; original global index 3866.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 33ffb68d45c9c346b4a2d36fc61a24ac967bdb4c7d926e1376a049b37e6e21ed; original global index 3980.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 0]

-- Original cycle 34d563f54cd7b8d131e88e97a07c6dd43b0f44baafeacdadbecf89bb8e5cdc6a; original global index 4041.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 34ed5b8c8734d89a7e00af825de48e6e76838bbfd0e2ce0b377afdf06cd9e281; original global index 4052.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 3513d545d006b31ccf616c2d3e98c1d7c188a3454d1ca12e2c6a3b5e26ebef1b; original global index 4061.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3557aad723391982e9e411dd9d54364a9e94fd54cc66d9a50710933a7e44e78f; original global index 4087.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 36abe96cdb18c8ffebd0f2d797d76c3a106aab2a3b9cd1076f469677b0e09fd5; original global index 4201.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.gapLower 0 6, .triangle 9 2, .triangle 13 2, .gapLower 0 3, .triangle 3 0, .triangle 17 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 3730b8b6e372ddd9685322322802ff539ea4b3a7d5b558219da166cfcce40fc2; original global index 4237.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .triangle 4 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 373594d5bbc34bb9f1cf3125a8e1993c4436ab8097642b50602392f6a7f47a9f; original global index 4239.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 37aaabdf59e6ee40f916f8647e6c69593ce1a4c6275998dbf18dae364c59f0a2; original global index 4283.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 2 1, .triangle 4 2, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 389491ec4695415f7a1b93d460cb3076354d29a66da124b21d2a468fefdf08a4; original global index 4353.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3c2a308c12a0aa381070194c040044c09ead85758cde47d1d042eae07f395993; original global index 4667.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.gapLower 0 6, .triangle 9 2, .gapLower 0 4, .triangle 4 1, .triangle 3 0, .triangle 17 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 3d3e23ee964b0c3e710771534cfa17de4d39fd71d6670f2e5722df2339872c24; original global index 4743.
def localCycle00068 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3d6042db716955e1db2b8b94e94331e722fdc66a86731f06c29fa2bd59fa5f65; original global index 4752.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3ef798f9e19ca6e90aae644a99ea8581a4016b512347e5a9482d719a4abfc734; original global index 4866.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4078572e0e854579e6aa022f8fd311d8879bbe7bfe8f5bb7a5dea2329d47cb92; original global index 4983.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 40a05061b741f8d04f356c61802f77e4df2e38d69e0ef494edecb86060f21a38; original global index 4995.
def localCycle00072 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .theta 0]
    constant := ![2, -1, -1, 0, -1, 0, 3, 0, 0, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .gapLower 0 0]

-- Original cycle 4266614f088427d2b310ee8dd047b93443adb68d18d6e0a7e145e2accabdea64; original global index 5115.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 42fcb5654366ea24ea8aa0be6fb39d30f11b88edbcd69365cef8dc2bca4dc130; original global index 5167.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 431a751521bc1e44101fb8fa0e02bf25455f7a69a77d007bcd57fa10644b4bdf; original global index 5180.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .gapLower 0 4, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 437ee5802645a12ae3d913694226011f4bb55a391c757cb02735713968e55c63; original global index 5213.
def localCycle00076 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 43d03ffdfa68eab87faa4c3dde43a1c409e70e99b0405be08ac60cc88de54a5b; original global index 5248.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 44549c54acd8bc9b0ae240633fc166192ae8f988b58868273e99a0eec8072fb6; original global index 5290.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 445dee3618c4d16b8fad62debe9674c6b6be43da1fb75c87b66dd87ecf8739e9; original global index 5294.
def localCycle00079 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 3, 0, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 44d9aab1de6b8cb9c44e9979d0d3b2c80f36b0840710dff2b97b763d814cc46e; original global index 5334.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4925a2b024ed666e8fae323cc6ad3450d698fadf07060e5b87849b29c70a1643; original global index 5665.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 495d2cb62380a87f1769021660646e6bf6b315066ed7c09e856ba17e390fdb69; original global index 5685.
def localCycle00082 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .gapUpper 1 3]

-- Original cycle 4c303edf992704785144b5f539ce5ab309279d32a41c0bbd4de641ca2a7dd521; original global index 5913.
def localCycle00083 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 2 1, .gapLower 0 3, .triangle 4 1, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4cbd447975c7b07bd311d5c273bc0471ae79fcc39f057a4c607243000f30e0d9; original global index 5957.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 4de88143a4841e40912a52fce8acc14f597a424fb102babf1070505963eb3078; original global index 6051.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .gapLower 0 4, .triangle 4 1, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4fd2866d59ffb8a244c0d0dd1aa9f4d51d7dfdb81ce8214d78056a4d26b46a1f; original global index 6196.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 50c9e5f343ac77a5f4e6a9e35be2069cc0d6843b190732de605cc64389cd6fdf; original global index 6274.
def localCycle00088 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 8 1]

-- Original cycle 514115b0a2b7968e6dca1ba145c82c82f68bddd6f25ba5ba8f30ca68194800b0; original global index 6318.
def localCycle00089 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 5 4, .gapLower 0 1]

-- Original cycle 54ca15206f5cef3ff0b3c00365a815a46b872a1952f78e22fb93fed7d6aa0911; original global index 6568.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 555a707b286989b9a7863eed30d68dcedb45705d663487c92160dc0084e98e03; original global index 6611.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 56db52f8c8531af31a088144a2d38830223a2257fb6aef5a3fd79ef1435bf96a; original global index 6737.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 4]
    constant := ![4, 0, -2, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 4 0]

-- Original cycle 571e8adc6f5027a4130092d53eb6bc38bca596df09862aee8a6940dbd87a463e; original global index 6752.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 4, .triangle 14 2, .gapLower 0 2]

-- Original cycle 57adcd5b2f6a526ead984fc82264c298a768ba409099847448869b7509d7b551; original global index 6805.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 59f03053b9d60a39b7dbb9589d4de7f29e8b05e071bdc304c9d4441db75f2435; original global index 7000.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 5a854fac1711a73c226230bdba6aa4e0be193f0417799acc4625eaa7b03708b3; original global index 7048.
def localCycle00096 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5be7fbda656183eae6af4d802ca752c118f27a412a304c8d6549eba4be56e96b; original global index 7147.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5e72e02d86b4dcf970b946c182f1d509b3c44ccea465874396a7e8054e853cca; original global index 7349.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5e9d348df1212f9d94801397a756b9e8e43fc62f0e6243bc876b988d9856a847; original global index 7357.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 5fe6fa77ce3670e737cd1ab00e207f42c4036075a16146a4be7d7286a47f4351; original global index 7475.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 61c013adcbbdcaa017c9de286a13ddb959bb98ee90330ed2758acfa446eed26e; original global index 7629.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 626dfeb6d08a09e6c7bae803878a817d5c3a683e74e5e1a2cfd229049bdb4f8b; original global index 7681.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 62dddbf106d5a200f6fcc623a15e9f3b1d634c127ad883631c7c264003addce2; original global index 7714.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 6327769f6424729962adaf8f06cb2eaf54965ec573cdaf7b07f5fc60e4d0b4c0; original global index 7732.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 4 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 632887b01b4c0249962f9417936e186d7790bbdb2bef77064c4ac06a7cfe0143; original global index 7734.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 63c9d03a2cd766ede1dfbae270fae5508e45fc185f8a61340393c7c692f1bc75; original global index 7777.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 63f6d62995bed6aa11842b59f753ab90f82ff1a6ea2a6d970dfcf17a0d32fefe; original global index 7792.
def localCycle00108 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 65929059381e8402ee0a3aedeb6391bd9bf061e26fe588b11ed2717e075822fa; original global index 7901.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 6739fde362135a77e7de3303752135f3a1daad171a7be349c09799f327c0b491; original global index 8023.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6b83367e424da3c38a40a7b78678829c327c18fc50ef72cfd98b9708e7b50849; original global index 8370.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 6d7e8b14425b8f713b5d75b99ee25b292a540e5458e9b962cb4cbc41d7e1c886; original global index 8511.
def localCycle00112 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 4 1, .gapUpper 1 3]

-- Original cycle 6f7f88b17745191913af31a13d402716d78dc50c69cf99dec700d3e45452d6a6; original global index 8648.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 75e2abb1c991c4225518f888d1693672b28bf2cb3941646f9c0c595c13425eef; original global index 9134.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 75e8df46fdbcf6cf13afe3ff8c29b79853307d2dbf04d149dceceb36d60516d8; original global index 9137.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7833df63b731e66789c77b2503e6b4d5a368facb9e0adbec4aab058cc5afaf14; original global index 9289.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 78aece13b267f308be53fd2965f5d1618875e06265cbb438fc4c8d1c6a294c5f; original global index 9336.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 7a03c0c8c3fd1b63630122cdb6f1d7b68ba2fe5b8eef517341c6c6aa3b9e99b4; original global index 9437.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7ae3e4df0201026f0e988bea12823c1e6e0b99cbed8ba373ef677aa8146f1818; original global index 9513.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7db4cc8a7204c7e7e838a150d5e5c02873893378c693b2832ff18b72f81e90b6; original global index 9757.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7f6412be3fa67a3977e38cd73aac48d8976a17050d72976ff8d9b7cfb91c0048; original global index 9880.
def localCycle00121 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 14 1]

-- Original cycle 803e28de68153560c02961ed3e47a04817a2ebe3db06f20c3f9091c68cebc4e5; original global index 9949.
def localCycle00122 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 3, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 80d7b618a5b5e93b4d720be7e4318caa4758d85605898e437a07ec0ba4e63b84; original global index 10001.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle 83986cae57bdea91fdac6464e214d58b8896ee1bbd986d9ff1f66304b33eccfd; original global index 10216.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 84cb6b6027885a9f0474caf9ff2333654247045d03101f5f3a07ef4da068d93f; original global index 10310.
def localCycle00125 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .gapLower 6 5, .triangle 8 0]

-- Original cycle 8a1ab20b49bd68c118f72b3bf5cbd23cd3175b82cd84b0ad7d916c6605f14212; original global index 10704.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 8 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 8c369ed5234554b3e7e46030adad0afc516db5304d58543099de0ea8e7c913a6; original global index 10851.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8cd31595d85306ae629a27c2050a78ae499b6775cdccb9868361da85ec9a5d9b; original global index 10893.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8d10d5f2234cb69deb68072d816e4c58e569833b603c37fd22a8ba830a339ff5; original global index 10912.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 8db871cdc111e8835c57e60b7463ddac4836cb9634254c3794514af0daa1cdd6; original global index 10964.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8dcdb4d1c0f927df170f1b7fefdeb4610dafe05cae0158618291c58424db021e; original global index 10974.
def localCycle00131 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 3, .triangle 4 2, .gapLower 0 3]

-- Original cycle 8e05debb123ab290b1f20eb5cf75d8677ed77807ea66b9e7f07e361b6ca75719; original global index 10999.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle 8e1aee8b27e9f99a9caef946a5dc728b32e9125e5a7f733c1244acc92842a6f5; original global index 11007.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 4, .gapLower 4 4, .gapLower 0 4]

-- Original cycle 9093ac1cc2cfa607d36fc19581438c0988f74a069f774ec8251f0399d1ce9b7b; original global index 11191.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 6 3, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 91cb9850fd910ec41a3c24de4e147f1d854318f2618b54ff3b6ca2e46d6ef7aa; original global index 11299.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .gapLower 0 4, .triangle 4 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle 922470d9859b49ce4e1176264df5fc7223f2cb436afa78e7f301a73d29a3db93; original global index 11319.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 92b952cd80ee9927143e475524207fc029985f7337a0d8b25027e3aede8ac28d; original global index 11369.
def localCycle00137 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 14 1]

-- Original cycle 951c4a9ae9ba4fd5b0e8956870d2112b4b704ea2b33aa22b5a10309203b99ee9; original global index 11583.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 4 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 95fbe6e040800a931df53f7d4155e686465fe1255727b2dd0fc7e8d18edb0651; original global index 11662.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 0 5, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 0 3, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 97214baa640cee11bc7f283cf4be92e27fef6f049b5dc932e8f0d95afc6aaa6b; original global index 11745.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 99f13d3401f1939f3272a28f92502f44fea03d253f25750103ba4b0c99d8cad8; original global index 11949.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 9a737df99cf76b529b5d27799ad1373f4ef68a5ef1cdffa62f617fc21f762705; original global index 12000.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 9c09cff30e8c9d6e49f7de26c970aea71ff3f7cd2531d27b93ee00852605db2b; original global index 12138.
def localCycle00143 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9c16b73e3a18f6fb93dde9378f566c6ad01c0f64774b3149d30bd4ea9ec38ec6; original global index 12143.
def localCycle00144 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 9dccc4f771008661f5b9d5f75a159e4ddfeee4c770ce31ba2ff99072db412e06; original global index 12277.
def localCycle00145 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle 9e857a1e65b208d5ef44d2ffc4f9d295a7ea8c5d7b79e643be0a11faf3736525; original global index 12347.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 1, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 1 1, .triangle 4 2, .gapLower 0 2, .corridorLower 0 5]

-- Original cycle 9ef464c0cf4c66a176a055b84755b95f844c719517c2e165d87f33c443116cb3; original global index 12378.
def localCycle00147 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 1 5, .distance 0 1]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 5 3, .gapUpper 1 2]

-- Original cycle a05cf85759e2fbb24088bdc7704b9d3f6e4df5fd93c7b4bc08335048dc5ca8b3; original global index 12481.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a193ec904b715d815139694b800e553f591a0bc51469c685701c12783d96cca9; original global index 12563.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a1fe57f771416b7ffa9ae228487b313f78ae31303601ccc029a4ead805606111; original global index 12597.
def localCycle00150 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 14 1]

-- Original cycle a2c429632e2becce9a6696b4426989f789aca9be2f840dc69ca57730bf825b87; original global index 12657.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle a3626a67c5edb8833ea2b95059f9adc1cbb92be9d5f87d243dd92a911c19c3b9; original global index 12700.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle a37a46756f9798a38aac90c71804a2445ff4b2a7f2b3c519a9a5580e93800d63; original global index 12704.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle a37de322456dee4a6f1ecd8f031f556dc42f88a7e2232b26778fb8a0b8b82982; original global index 12705.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle a3b352f86dfdc3360456cfa9f69957fbfb7269ef34149b98f80cc48a349b2f30; original global index 12727.
def localCycle00155 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a4243872ffbceeb2465c0662ab0f595bf79871c240e5589686df2738d83532a0; original global index 12758.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle a4c6f7d7dbc8b3063a740c7677908ad5093dc421987a18473b0d8bb0ed0112ef; original global index 12806.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle a4e4264001169ef20f0e04d48fcc1f8ff86b65fbcdce7ae01b3a287ed860fe53; original global index 12815.
def localCycle00158 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 2]

-- Original cycle a5998b70a4e36cdaf51b8df9f54132b0b8a7084c9c3152e8f1a7fba2e9afa363; original global index 12865.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a6490fb39a56fa98f5094cff59cf84dc77a2391749bc933581e4fb5190100598; original global index 12918.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a6c7f85f2a8cc73d3c615f9e1aaaf6d645f8990f72735ede2d967f3b079e9c95; original global index 12954.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a8a3e9925975626e1c95c7bcb2bb18d413ae0c6543e6ae8272d8932b0a42538b; original global index 13120.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -2, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle a8af2252a2387d6dcc55a87621341419db91fdbcfb8a51578fd15078407a9816; original global index 13127.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 14 0, .triangle 10 1, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle aa43858134f2f5d8ce87e48b93724d9d6bba64eae715a1a345a2efb799dd088a; original global index 13256.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle aa4bf198268a0f947f08f78504f7a237be7b6c687cfcdf895b4409d8477de16c; original global index 13261.
def localCycle00165 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .triangle 14 1, .gapLower 0 1]

-- Original cycle aaa868f3e31a6c2f8ed11c826242220891da1794e2bfe98d756e5cd8ecaad4c3; original global index 13297.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 2, .thetaLower 0]

-- Original cycle aca7de20e1c101e7a2492d18a4a0aac25323d2b535e6d1e0b3291e0cc380b0dc; original global index 13461.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ad84d27d006353ce0840361a48fa3f9903e8d9ff5eca8f6d2780fb0516e1f64e; original global index 13537.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ade52fc9ddba045b1d4dc5fdd869c0fcf17ab1482a8634cfb0a2e6fbf8adc981; original global index 13569.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle aed0b83bc875f01e5d2a5691f0a5d1e896f125a15476453e23f3a19366f6af1e; original global index 13645.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b03c1b4d343087020b86382034c6831388843f98d7f13394842011e1ab969810; original global index 13758.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b0d3f08e60c141212891a90b313becc1822f2a820ea1d3898c3be2fff0dd3c05; original global index 13809.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b1117692d2b9a42fcfb4ade47587681b62861dcfe5a5f3f8461f95a8f557b933; original global index 13825.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .triangle 4 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b14dad3719c226508c174ac7ef34614829b5133ea3aa965c42b8a0bc53ee15bb; original global index 13851.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b2e09947a83c0015b0c26753216fac719bf219f55ef23b82e041d94c8570d7bc; original global index 13981.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 3, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b3ad1e3ce670e2ba4a5f361277754137f6e151a419862005d8ea77f6ce38aef2; original global index 14034.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b479cade5bdb8902a254e6facd66e9fccd32d173c091e836081f89aa8f2a7934; original global index 14097.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b56d3f928f522bf3617b2d62d050b96a5e0f1a56f49a6ef42c12446e38d4c5dd; original global index 14176.
def localCycle00178 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .gapLower 4 0]

-- Original cycle b6d6ce63d713cc024507ed6b03d9ac9016b37663a1b82ee5e6f11bde97e3ab74; original global index 14286.
def localCycle00179 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle b7f299163ebf7e287e707100c9676e8694dffbd0b7b915afdfd7af989cf7990c; original global index 14352.
def localCycle00180 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 3, .triangle 4 2, .gapLower 0 3]

-- Original cycle b99598e2e6cd94e1944fe6562a401e96611c1a106654b9498816d933bc373b39; original global index 14483.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b9c00266fff0ee5880289e42ac540df2dc4bba5ddd99be0ab9326f604bd16be5; original global index 14498.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bb355ddc8d28f6d6fa0ae95cee9b9dec0591158fb2ab53f939915cccc3ac9e08; original global index 14618.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle bb5b907e3337121053332dbac9f6f2865d2abe12b1d59c362be87406c1144edf; original global index 14627.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 3, .distance 0 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 2 1, .triangle 4 0, .triangle 24 1, .triangle 17 1, .corridorLower 1 2, .thetaNext 0]

-- Original cycle bb9e93f21b11695e4b0e9243021cae110c43aacef7cfbe628a02ada9059e5e21; original global index 14647.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle bba95c97fe15a51a9da07c1e9d272d838cc23f3d4e12a6bc2ef874ae3d0f9153; original global index 14651.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle bdd805c855b6f38c433ae5f3689f5e280c09b661edf70938e14ccabf0b690e0a; original global index 14807.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle bde755592f903c15d39e06bef5748764a4f7b501db5176e997b49cbe7797abea; original global index 14812.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle c27c3c4b400818a8e30ae9e0c2e71c439d9ce7eb040737163f083cce420c34a5; original global index 15182.
def localCycle00189 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 5, .distance 1 5, .theta 1]
    constant := ![4, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 4 2, .gapLower 0 2, .gapLower 5 3, .corridorLower 1 5]

-- Original cycle c37a4f748fe87d452817ca4c5fa8bf99a312b6da6b6118ecab639f69c339d000; original global index 15254.
def localCycle00190 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 0 2, .triangle 8 0, .gapLower 6 3, .gapUpper 1 3]

-- Original cycle c380a57a89469cc0b0dfbc87a47cb666b27f139248cbe770fadefea91aea5886; original global index 15257.
def localCycle00191 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle c4a7b0f14e457a533266beb41a4e7aedb69a810c01872bf3a429352a3ed352b1; original global index 15335.
def localCycle00192 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .gapLower 0 4, .gapLower 0 3, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c5101da9b20e0f261afbfeb22af1eca859b3b1ad88075e956ced4ac29a9822c3; original global index 15376.
def localCycle00193 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle c54fd2b62417804ffa31efcaccf5e27a755e9e510d00af186040907f9d84d32b; original global index 15395.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle c580831cb5d5502c54e523c7bd0619f7ae5f130ac15039debd135f8f13d17efc; original global index 15409.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c7b80049ca7ee130b3ed14dc1df157053e116fbc9758dfffe50c1629faa7e1df; original global index 15587.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle ca5e60c41d577c5960523c3aeb0839650a1e4753c48b8ed5381775b97af97f09; original global index 15818.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ca856aa515c14c254548c04d1e001e9e0789f2207b1ac1db6e20f5013f542e84; original global index 15827.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle ca8d851d7279c02c2d6fc197ff5e30c4b7a3a16371558f31d1ec7956a46c646a; original global index 15832.
def localCycle00200 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 2 2, .triangle 8 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle caa5081144486f0655f314dbdd0bfd647cda7ca7840f78c14fadabb8ac07ed73; original global index 15844.
def localCycle00201 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 4, .gapLower 6 3, .gapUpper 1 3]

-- Original cycle caba4603e0dd75899d376142ced61f7b3e690a36a3841b5c7c43d92b2d581d78; original global index 15849.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 0 2, .triangle 7 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle cadb1fcb6b85649bac38f7d041e58722f02771c7792949846a94f3d6c96113fa; original global index 15851.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![4, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 19 2, .triangle 2 0, .triangle 4 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle cbd34337d209582b4e8c4dda8d796c63cc594712d3b3ddd5ecd322d4fc391a1e; original global index 15927.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle cc7d6cad3de2b9a68fdcef6fd59f1130aae6f3499bacb404cc0c3a283c926af5; original global index 15984.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle cd297c7b5cf1a010242b9413596474eff9f65b17aa6008f54a8ed074819ab034; original global index 16033.
def localCycle00206 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 4 2, .triangle 8 1]

-- Original cycle ce3e4cfbb89aa6ed3efa3484648832d6b8274f6ba64c0af796e9ead12e75f9d7; original global index 16113.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cf03686d23d0f9293f7209fb0977adbef6d9fa0cd4ed2fefa5bb40c31f211ef9; original global index 16155.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle cf9b78cbb0cacc764ea7d22d4e75ce7da5d048f210d5dc72ec4d609f2c94dbcb; original global index 16200.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cf9ebb27341e629918e7f446ce74941840b0d5eae67e8cb7de23665848c77656; original global index 16201.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d04414905b848fc5ad8d7d6fdb54352ed0190fe86587b53498457bf8c1024e51; original global index 16255.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d14ea7e9fc2c6c974e750c743003906ac21713dfbcbe4504f456b06375e3e949; original global index 16336.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 0 3, .triangle 8 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d350dfc98d82b2fd094942f527a1358bf074469b3f6ff8905c0d4381a02596db; original global index 16483.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d37db9c61f8eee6b905d8f2b170fc70f2b5c4c295ac453cf555323342a5c4955; original global index 16503.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d3b40c543f10ef9af51890f263e9e21fb3e1a9e6c7451985050fd7821ec156f3; original global index 16520.
def localCycle00215 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .distance 0 5, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .gapLower 0 5, .triangle 2 1, .gapLower 0 2, .gapLower 5 3, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d43f099bad5d6c91ced050ee754dd80ced8cf2d0637c03fdc7a3b4310a193a82; original global index 16562.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d46c17dc9df47d09f4e03c30981dd07f223adeb08ad05ead460655a8d656ff48; original global index 16575.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 32 1, .gapLower 6 0]

-- Original cycle d52873b9631e617527ab78afa0b2b72c7f7e8fb75cfa9266cbe436479e1ef1e9; original global index 16633.
def localCycle00218 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 2, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d68b2b3daea9c74f60be3e822a9807f477522235e8a0191f996a0081e090bfda; original global index 16750.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d8e6a81c411934410432a96704b9b78dab58cf61143f3c9d9b70ee8f8fda4e2a; original global index 16936.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle d92c6c594e1e4558077cf5080121cdc7649bef6f14cc3bf93ffee513eda35842; original global index 16968.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle da66b9d17e3971878003b99d132516da90e619bb9ebcbf268d963c6ece911b87; original global index 17068.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle dacf621d504821f85da7e39b920077668886ba731c21017f8becd260db023821; original global index 17099.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dae2a57dd975f0de41a26e9e4d89cf487d2e775b18414db224f0f6ce3f4250c1; original global index 17104.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle dafcad7c93edb8479dd3e5a8eac47889a581d66c11b5330783af4dca647c60e3; original global index 17114.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Original cycle db605bd9fb690e173a9984420cd4331503a8f6c00a09a3fb659dfd859dcb3f3d; original global index 17148.
def localCycle00226 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 0 2, .gapUpper 2 3, .gapLower 6 4, .triangle 4 0]

-- Original cycle dcffb9d3d1aa044e2191cc90a68dcc087913d39211bcfe616137bd1a3956b595; original global index 17276.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle dd431987a3a38f1e260f2e0a1d4ffadb7e45ca0a63a8d75d601538c86a242c8d; original global index 17301.
def localCycle00228 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 2, .triangle 9 2, .gapLower 0 4, .triangle 4 1, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e138ece017db1ea80b6c1f89d238257ac58286b5d7c9beb0de64af0d59ab4345; original global index 17613.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .triangle 11 1, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle e454a0c2d66c76fac5531128903e26d61cda46d9a9b6ee2f23b1b839c5ea78f2; original global index 17849.
def localCycle00230 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e576537a2814eb05f753fa733813f1bfc87bb77f24c9248c13d1c533f7c3f4b4; original global index 17944.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e5df1403cab017b70e0e6e02cfcfe427bf7e71381e54545cafdd21f0ffb7900b; original global index 17984.
def localCycle00232 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle ea75b127e1a9dcc3ea8e58c1add7bcb549dd2ea57a7a653be204c95912922de5; original global index 18312.
def localCycle00233 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ea7fd56bea2bd372dc05a10441760bd5ffcbbc64de374ff74505bf646d6796ca; original global index 18313.
def localCycle00234 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ec0fef1f90d6125f6c488a585c3b3443de3ad4f07c6931b6360b3dfb2566e7f7; original global index 18424.
def localCycle00235 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ef486796fc65e048d1215d0576f165c522ce0c1c766b135c8a25e8fd8caa958d; original global index 18669.
def localCycle00236 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f744a3b751a6b664abbbfaad0ea8a36b0c893e9ab617f7de81d8a334a7fec761; original global index 19288.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle f7fff58d05900072d2c62591bcfe2e9fc571566051055d67866b67cdf5e76062; original global index 19331.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Original cycle f822f5634d050ff714b9130ccfcefe82dfaa360bc8e6da9d471c7710cb7a16f8; original global index 19349.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 1 0]

-- Original cycle f83049219e11cff9f8b40d18fc59e9e4c85628922ace1c9fcb2922fa9401eaf5; original global index 19355.
def localCycle00240 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Original cycle f8346ca842c1d4fd7fb983de894abe8e06e1d14ce1a7a1f92ac9105e23363d3f; original global index 19357.
def localCycle00241 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 3]

-- Original cycle f9251e24348a15df3d1a6a5127f3ec390c27721cba24565d26adbe4d1a31a4c2; original global index 19431.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle f9c1c94cf25991e55744d10684657e81db6bdcedaa9c4c02691609014c6a99b2; original global index 19475.
def localCycle00243 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle fc501a514a2c3a5ad45d5ca244d0fe7bf1dd7242e108193738ca4f27606fab0e; original global index 19709.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle fc84e39f024b2dd2502b83cd35a06a5a8a1202c17b75cbeba68ae826ce724e43; original global index 19727.
def localCycle00245 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .distance 0 3]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 9 1, .gapUpper 3 3]

-- Original cycle fcf8086b9654b4c9c2cc2195ce206d63a8303a4c04a5444b6a9370fd47908536; original global index 19769.
def localCycle00246 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle fd6a0eb345dd7c3f8908644583c3dcc3277644f313a3ebddfb3c49e64c711e5b; original global index 19805.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle fe8d6cbb92be451d55fd04144fdca9ac7f3b22bfb3f335b01f7c8bab07343385; original global index 19901.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle fead5203b6f34045a16fa98dddb62e68ff60cb9503223bf2ace83fdc87770522; original global index 19911.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle ff20e475e9a2eb2d51f5b232fc4d7d00d4e84484ce25ae826190bd4dee84c55b; original global index 19947.
def localCycle00250 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle ff5ad726dca231bcba56b99820d97343990413c33f848de61f5ce085338de681; original global index 19963.
def localCycle00251 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle fffa72a30e2a93711923a63730ad99048433e968ae70565e117247ff76edfa26; original global index 20022.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

def library : Library := fun id => if id < 126 then (if id < 63 then (if id < 31 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 23 then (if id < 19 then (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))) else (if id < 27 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))))) else (if id < 47 then (if id < 39 then (if id < 35 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))) else (if id < 55 then (if id < 51 then (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))))) else (if id < 94 then (if id < 78 then (if id < 70 then (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 74 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))))) else (if id < 86 then (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))) else (if id < 90 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))))) else (if id < 110 then (if id < 102 then (if id < 98 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 106 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))))) else (if id < 118 then (if id < 114 then (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))) else (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))))))) else (if id < 189 then (if id < 157 then (if id < 141 then (if id < 133 then (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 137 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))))) else (if id < 149 then (if id < 145 then (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 153 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))))) else (if id < 173 then (if id < 165 then (if id < 161 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))) else (if id < 181 then (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))) else (if id < 185 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))))))) else (if id < 221 then (if id < 205 then (if id < 197 then (if id < 193 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)))) else (if id < 201 then (if id < 199 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))) else (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))))) else (if id < 213 then (if id < 209 then (if id < 207 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none)) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))) else (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)))) else (if id < 217 then (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))) else (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)))))) else (if id < 237 then (if id < 229 then (if id < 225 then (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none))) else (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 233 then (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none))))) else (if id < 245 then (if id < 241 then (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))) else (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)))) else (if id < 249 then (if id < 247 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none)) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none))) else (if id < 251 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 69 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13696)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 194 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13697)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 74 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13698)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low0 (![130, 89, 147, 131, 85, 20, 154, 36, 38, 180, 228, 245, 60, 166, 36, 36, 36, 36, 139, 31, 215, 17, 192, 29, 61, 135, 67, 13]) }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13699)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 108 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13700)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 34 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13701)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 55 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13702)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 34 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13703)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 208 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13704)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 55 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13705)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 207 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13706)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 57 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13707)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 57 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13708)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 120 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13709)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 204 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13710)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 2, 0]], proof := .tail 168 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13711)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 2, 0]], proof := .tail 204 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13712)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13713)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .low0 (![130, 89, 189, 112, 21, 20, 154, 36, 202, 212, 133, 245, 60, 107, 36, 36, 36, 36, 175, 133, 64, 146, 133, 83, 19, 75, 133, 184]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13714)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .low0 (![116, 165, 93, 112, 21, 20, 154, 32, 202, 212, 133, 245, 72, 200, 32, 133, 32, 32, 175, 133, 64, 146, 133, 83, 19, 75, 133, 184]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13715)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 141 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13716)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 204 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13717)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 236 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13718)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 214 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13719)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 199 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13720)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 204 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13721)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 236 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13722)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 214 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13723)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 248 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13724)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 149 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13725)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 243 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13726)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 239 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13727)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 220 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13728)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 222 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13729)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 231 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13730)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 238 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13731)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 209 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13732)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13733)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 238 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13734)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 246 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13735)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 74 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13736)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .low6 (![9, 106, 129, 8, 206, 39, 205, 185, 217, 79, 226, 125, 218, 140, 229, 226, 125, 10, 183, 226, 125, 173, 232, 137, 223, 52, 226, 164]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13737)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 57 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13738)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 156 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13739)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 43 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13740)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 2, 0], ![3, 4, 1, 5, 2, 0]], proof := .tail 23 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13741)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 1, 2, 0]], proof := .tail 37 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13742)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 240 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13743)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .low6 (![177, 58, 251, 82, 88, 39, 195, 4, 105, 138, 122, 125, 96, 105, 134, 4, 4, 4, 117, 3, 3, 3, 7, 125, 59, 121, 46, 164]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13744)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .low6 (![242, 210, 179, 190, 191, 142, 99, 216, 87, 35, 241, 0, 71, 203, 35, 213, 227, 227, 126, 188, 113, 113, 201, 35, 35, 235, 241, 161]) }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13745)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 141 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13746)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 23 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13747)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 37 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13748)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 47 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13749)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 172 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13750)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 240 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13751)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 225 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13752)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 104 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13753)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 144 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13754)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 40 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13755)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 152 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13756)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 84 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13757)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 132 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13758)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 84 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13759)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 26 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13760)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 132 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13761)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 186 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13762)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 84 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13763)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 84 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13764)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 57 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13765)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 156 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13766)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 136 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13767)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 43 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13768)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 176 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13769)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 204 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13770)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 244 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13771)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 181 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13772)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 51 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13773)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 22 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13774)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 128 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13775)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 141 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13776)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 204 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13777)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 244 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13778)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 174 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13779)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 187 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13780)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13781)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 178 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13782)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 11 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13783)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 103 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13784)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low6 (![124, 150, 24, 169, 66, 193, 42, 102, 5, 211, 65, 145, 18, 45, 73, 198, 145, 62, 100, 171, 145, 163, 162, 145, 50, 14, 115, 145]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13785)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![86, 196, 90, 169, 66, 193, 42, 170, 16, 127, 98, 145, 114, 6, 78, 49, 145, 159, 153, 48, 145, 28, 162, 145, 50, 14, 115, 145]) }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13786)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 233 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13787)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13788)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 110 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13789)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 155 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13790)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 167 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13791)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .low6 (![80, 81, 158, 8, 148, 15, 95, 97, 219, 101, 101, 101, 101, 30, 33, 63, 94, 94, 224, 252, 119, 111, 157, 221, 54, 92, 44, 53]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13792)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 68 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13793)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13794)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 76 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13795)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13796)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 230 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13797)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 250 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13798)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 118 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13799)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 118 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13800)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 247 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13801)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 182 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13802)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 160 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13803)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 25 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13804)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 182 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13805)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 160 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13806)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 151 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13807)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 234 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13808)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 237 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13809)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 143 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13810)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 1 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13811)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 12 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13812)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 123 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13813)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 109 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13814)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 197 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13815)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 197 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13816)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 91 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13817)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 249 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13818)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 27 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13819)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 70 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13820)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 109 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13821)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13822)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 91 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13823)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13696 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 13696 ≤ id.val) (hhigh : id.val < 13824) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13696)) = true := by
  let j : Fin 128 := ⟨id.val - 13696, by omega⟩
  have hsum : 13696 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13696 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard107
