import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard173
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

-- Original cycle 02c07502faa036b08e63006cf7ef0939feee301b4ef3de9a365a2b425c7a06e2; original global index 217.
def localCycle00001 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .corridorLower 2 5]

-- Original cycle 0396701810f0e6a26caad2b6e4687f46e8ce13c9114f1143ede6bbf39d75966d; original global index 291.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 04d3eb576fac0ff7b6b4d8557b6ea4baced875c59b0708f1209df90822ce1a0f; original global index 388.
def localCycle00003 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 04dd7e7b857d868b69c551de56f704ab72a01d1391153a6fef2a3b4224688339; original global index 391.
def localCycle00004 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 11 1]

-- Original cycle 05c4088043c45fcdccf6e6f6b176f82c4eb2d27a41d613e82c1aba15a57aeb2b; original global index 478.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 07be26362c4849f95c882795946e57e5bf9952f192e9988829c171ead0231ba8; original global index 630.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 09ba1e00ba05bd361fdec9dbd95817d0c4476d2f4adcc31abbcc8d0eb6993630; original global index 778.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 2, .gapLower 6 2, .triangle 21 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 0de987c97d87940bbb603a9faafe8e7f0410239c4ed520f8bb4ca5f14b96a545; original global index 1096.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 108826329de2ec455505a6f1d6ae1f249a6fc73c78f59fd39426e8ccc0d7ea44; original global index 1325.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 1, .gapLower 6 3, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 11cdb166821ff96834a8e525309a13a6f3a348083c0bf92bc094369cd7fec29b; original global index 1418.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 2, .gapLower 6 3, .triangle 21 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 141bd0687b1f1d02ee17eb54ca1aea8390a49139a99e588f666ab0a46aec0c40; original global index 1589.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 1b0fb5946944fc169c84c05e5aa54329c64374a8553a009050c8f4d09fcff7c0; original global index 2092.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1b1ab460a6ba860217d6564e8eaa96927656717897eab58d9c32b1ff389dfb8e; original global index 2096.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 2, .gapLower 6 2, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 1c822914a743f1e2bfc11632adee52be033f1bcae5c976a232e31651c34409ac; original global index 2189.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .triangle 8 1, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 231614361c32cfcd82071eb1239609fa9cae781867056e939e4814a9f8776036; original global index 2694.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 239205d1a57002940c73b8ff89b1fee183292101600401c88fef460b0b4a1f3f; original global index 2729.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 255aa40322e6454ff7ac44cb7051b7be5f4d4b615796661e2839beb0b8be4505; original global index 2874.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 2, .gapLower 6 3, .corridorLower 1 6]

-- Original cycle 2750b5ed5f966f617a720db5bf2384ee647c3553d3f01d5f2471317e7c17f30a; original global index 3010.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 28398a280fe75ff562fa3d8a35a15e4f22688d6879d27a21e14333362595fe45; original global index 3080.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle 28a2e269d4ea0021c4c71b5a22253045a70cf8c662a7b8506d195091f692bf70; original global index 3110.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 291d210e121858fbe5d9ada453f83d2bb3bc9b3a84ac94cd7d4b79352622831e; original global index 3140.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 2a1b8ec51f6546b1f146cac7492f66a5e7c6011e32d7a17e49ed7212f25df321; original global index 3209.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 2c2869b3c1bcb9804dfb08a42a294b2f546b96ed565ddd0e494b3751f7df16c6; original global index 3378.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 2cf875e2b154e6b1bd4b6196d1ca0f52508771e0a45f81cf64230e90d1d63ec1; original global index 3435.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 2ecdcf9c4e0e507bd51b46d0d28b2c16e3b1757be9b33064845860c9613b272f; original global index 3582.
def localCycle00025 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 11 2, .triangle 14 1]

-- Original cycle 2fa513a2fed756af43822d9e61dccf393d0515c854ae1e5b2a8e2ce8f5f287d4; original global index 3642.
def localCycle00026 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 393025b202d16ff6bd94cee5a004491cd81d13406ce51188839ff193f60932e9; original global index 4401.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle 39c3961428efb34716302765ed1f6b969398ac01e99c31fee7a77eae8c800276; original global index 4457.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle 3d74a98d259b8c6b1d44d3cdbe9d93617792acfdc1bd7c50533df6fec5129e6a; original global index 4758.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4019bd9ba1e07ca62a49dd9c7b1861557cdfbe0bc6d0a5eb661081571b6eaef0; original global index 4945.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 42e57fe5a431b2a503a44f28ce592d5042bb19dacc4efd972c8fd3227d6ba9ca; original global index 5151.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 442a83abd57d539403bb76086bc11cb86c18be9cd5b031bbc2fc54a5ee50219e; original global index 5276.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 46d70da64e4ca6be6d74479aac48f6e4c3084fcefdfb9e90325215d6142f9108; original global index 5489.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 1, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 4b0254298c45c98c7eb0bcbcfbd4e7093653b0940ddad0d82aa8d9ddf5ecc636; original global index 5822.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4caded7ec9b914246d347288090bea7642ba357cfeebb1674b821272458f4b95; original global index 5950.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 4cf9ea4b0cf5d018f7566ea5ac8a32e369141c1dddb040184208781230ba6771; original global index 5980.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 4d2c87be247103ba268b6d2ca77e96b4cbca789f660819b1dbfa2ed70804c99a; original global index 5991.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 4e6b3b3aa48fb72fca641ccaafbc7d2052d67691e4ca3ab692a2cbee8e47ae3f; original global index 6089.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 4f104b319a58ceef13521d6d12c8367f1317ec45256b75729591117ba732504e; original global index 6141.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 51fc48ae9154c9232037039abc7cda102a362a9fb41292a98baf4fe666b54a7a; original global index 6376.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 530563f3028588e7920c067075436ec6430d3b7582852f5dc8fd95d8f0177a14; original global index 6462.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 11 2, .gapLower 6 3, .triangle 18 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 55d504c4eac80d3719f57dc0c11712512c2a91e4d4f26930cecce773fd604f98; original global index 6654.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 575923ee4ef952f0535c4539a2de5fe41b74f1cd7374217af2d77709213d84fc; original global index 6773.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 57b99aa18b32d188800cf12885b27862648f75db4691bc170723963028626e7c; original global index 6809.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 59d4a2bd221573ca473be08521d919f08fc29fbf8a2514059c714b05448965d6; original global index 6988.
def localCycle00046 : Cycle where
  length := 17
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5d0a2bade223d71261d4162ff70a2a7fe0f92ee24b11f09d96dbe784426eb812; original global index 7240.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 1, .triangle 18 2, .triangle 21 1, .triangle 32 1, .gapLower 6 0]

-- Original cycle 5eabfb42ef81291ad8ebe3d5c46f997f1ac81b46eba5f4158beaaca45ae985fc; original global index 7366.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 5fe1dabdd9f8b04f57eddc95c5536879813b30ed23c7906243c3ce0c189d7d5c; original global index 7474.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 641fb7c6dd386b62dde8247cb00e339a66e14814198c3a6428551f9eb2195e99; original global index 7801.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .corridorLower 2 5]

-- Original cycle 67d139dd7c286f2f642da3ad85ac50706d961737f7da10cc497938baf0301092; original global index 8068.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 67e26fe9f7110329a90e779098e886a477253260ed1c10e8f54d7b8af912cfde; original global index 8076.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6c7638339f983fed710553999c74c10d68340f6d0e27936a14ed66b142663f64; original global index 8444.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .gapLower 6 3, .triangle 29 0, .gapLower 2 1, .gapLower 3 0]

-- Original cycle 720134dd867e27c643ff55d35b78d237e4fd4613bb67081bd29b361b55fe6257; original global index 8835.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72e3033cb6064cb24555331b9bc4e97305526bdabcff8978f66ead0577dd202f; original global index 8902.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 74cc12a4acbd55ef7553b6a9ef1299e8e0a8eee039a89e6fb9b07cc095b1c662; original global index 9047.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle 75408cecf1306eeb51b538ffdc0971b4d2afcaf30c123bc31b1e07acd3adeacb; original global index 9085.
def localCycle00058 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 10 2, .gapUpper 5 5, .gapLower 6 5, .triangle 11 0]

-- Original cycle 79ed3489d8cd2a409e4e08a21361912f16813171cd90638686ff3527ee00bb2c; original global index 9430.
def localCycle00059 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7db8db0fda5428e2f3dfbe7467836818fe3e598d0a60a90001fa4e33a3d6ced5; original global index 9759.
def localCycle00060 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7e43576266b58c3e4701c320946e44c8e67a0a33d41857a03794d395f9ecf833; original global index 9807.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 7ec6fb50128e005df3c7951556d41334bd683c7c26fd88485791d971c7622cba; original global index 9846.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7f5aec1617c5971fc2fc9ccc6b1b13e9439eeb5c00471e60ed05ea9b2f820372; original global index 9876.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 80914e84b171bdf0530493ecfc24a1d270b02ab9bf7657991d3b9439d8b7ef23; original global index 9978.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 2, .gapLower 6 2, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 8118c3a5f7852ea01a6336b87b4160f904a12d9f394bdf1d570efef26cef7e84; original global index 10018.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle 848b58277f10a9075d3d1f505aea221e38484a0b6219d025b8cd180e8d0f3139; original global index 10293.
def localCycle00066 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 26 0, .triangle 33 0, .triangle 34 2, .gapUpper 4 3, .triangle 25 1]

-- Original cycle 85beadd09ce5d1e845a18842d00d133151387994901b4056bbe07a5ea7d1a11b; original global index 10380.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 85c24fb00a4109151919bb93520b5f47198c6b7dcea1bc5365b62db2f330aab5; original global index 10381.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 2, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 866f14a63773d35372f9f0db590a60553b5506fd5c0926a2f1ee8e38621940ab; original global index 10423.
def localCycle00069 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 2, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 867267ae1d3e360ed5d55b9e577b10c56a5b3773d1303c581a713b36a72c7657; original global index 10425.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 8691298f8df3545b41d4e2d3a080200183b774b37305b418316cc772bdbaf3f5; original global index 10431.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 875b4858e26b7d4417e770bf8c9b748253994507002145082bdaa848ff1eac60; original global index 10498.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8c36e02e866222ef443f77724a8b3282001f0876233263e1dd177a2983fb9fa2; original global index 10852.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 3, .triangle 15 0, .triangle 17 0, .corridorLower 2 5]

-- Original cycle 8ef600f5ee1edd425764fae4309f09cb1b10c1d85f1dbb999865946985f82549; original global index 11059.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 0, .triangle 20 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 8f97409611d5f769bf824cc25a231530182644804edabb968ba04eaf95a57348; original global index 11114.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 8fd5679ea8f77bfacdb934f2c22756cb35736d4b5d273e9abee9028110605d63; original global index 11134.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 90211709345137079ca62ccb12f97c25e7a844bf7e9e00551d70bd8f6e4b677d; original global index 11154.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 917c5341184ab55e10e0f52a9faf56fe77ceb3e72d2a1fa80504fefd15ea900a; original global index 11269.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9436676753210a3094b0811320a90b378373019363dd260ab87ea08fe0289634; original global index 11496.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 94fd208d8877f120fcc6a5d19a6c94e2ddabbd6922821f7aca042009f22da297; original global index 11564.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 96afebe98b82fcfdc85bbcc916f678bb58b0b94361e82cfa9518ee154a82e15d; original global index 11716.
def localCycle00081 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 970561fe2fcc4f213a05e01ac47824224d2a04b4fcc7b7677d08d2ca286ddd75; original global index 11737.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 99f4d6b13c1c5c464270d5808d97f6b2fbc2bf7bc2dcdaff478ecef7b3e4c434; original global index 11953.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9a31ee91a5a2cea61b0b95178f39ea5a21428cf086cc7fc5bc5e572c8d2bc688; original global index 11980.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 28 0, .gapLower 4 0]

-- Original cycle 9a737df99cf76b529b5d27799ad1373f4ef68a5ef1cdffa62f617fc21f762705; original global index 12000.
def localCycle00085 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 9b5bf6f3b94a6e3a0009b77d91f2e4b6e228181e8f7e9a7f03e88b5127626899; original global index 12084.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 9b6c03de517826a806f7a6e192eb175c26ef456367d8bfe004133005d801d474; original global index 12087.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9c1539122ef4a1ed3b36db719558bb854f5a7dd7b5cd57b4570be851cfc38d74; original global index 12141.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 9dcd4c2f559a3dcb4eead1d50889357ab376245526840e32b609ab6c94ea73f0; original global index 12278.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 9fe881ef7a94dae9341179f7dad2ae1e33e0c71099f0e461f266d89943e4bb84; original global index 12448.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a46b8dc648d02d2469682f850648a9f3d4b13af3d1a8e1817d981de108197eae; original global index 12782.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle a6c7f85f2a8cc73d3c615f9e1aaaf6d645f8990f72735ede2d967f3b079e9c95; original global index 12954.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a761f6d7e0662ccc5d19c332394b913137771b521da4ce5649db9a88b682e941; original global index 13022.
def localCycle00093 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle a8611d5cbb4a8698c66fddd9632f551175f794e212c61b628044ee6f099c60f1; original global index 13105.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle aaa0eb48f30b98ecb1582f60ff3b336d4e4d6f5522c847f111bff53470529365; original global index 13295.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ad6b656671510d94b84e3f6f370861ba1f253b99833c74874c82daf0575458d9; original global index 13529.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 2, .triangle 18 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle ade3dc410d12dcf8f51ecb5f883e56fd5905d8118d05f17d8e1d9ec0529eccb5; original global index 13568.
def localCycle00097 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ae0b49a14c77cf1a076bc16f90da211ccefd2a13a4005a949d4f1869e8c63753; original global index 13579.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle aea3c0981c07ec4854a82fce302082e054ddbe0f13a97bb02c823de258eaf93b; original global index 13632.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle af245790b03776fa493aa4bd5cf943a9cb4e92c011817671110cb58dd0376e14; original global index 13678.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 17 0, .corridorLower 2 5]

-- Original cycle af3e50f90308169c245a4d5058b2ae25d33a249bddb21faa9ea9652d385f2d39; original global index 13689.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle b1776d85a291c80310226316c623987bf0c45f468097b1289ed718f5639aa2e3; original global index 13870.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle b1c15f3439a988ca1451874963f39d17d49c2a85d940a3c948b2363e9b666ac9; original global index 13891.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle b1d0b56f6ee6f0183955834b691b932b720abc89792a825481b13f7a11e52f2e; original global index 13897.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle b3d81efda3299e1821a5f8eb54cdf3c6df54b7714ec5ccc537c9c3788c829d84; original global index 14044.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b5a2e55bfb84480cbdd3f61832fea6d867a3bdedc2ca741e7e1375aa01ac4e5c; original global index 14191.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Original cycle b7d65cbaadd48fd984478852fcfdc942035af6f48376b27f944f85c2730068ce; original global index 14344.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 18 2, .triangle 21 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b7e2628422aa1136d2abc4d2094038ffb82a235c2a1f7661bae94a9d6363f432; original global index 14348.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle ba61fbcaa87c362404c5b8ed8f5e9feaab2975a5d1732154d6bcf12e9830d352; original global index 14555.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle bb8ea3c2afd2b8d15aafa6fe6fe7f6c17d573f6c3cc98ebed51bff59afb4cb76; original global index 14641.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle be2a2c7738f7c23f9a5576223973d8bdae2b953ee41b2156c4b30196562b1f72; original global index 14833.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle beb436ff158b337b47e9975c9dcb99e420113db463bacf091b6d7831e19c7b51; original global index 14878.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle c02b431c96d970e580e5b1d48993db1d9b6b2694c2c7597d812673f7e84cb363; original global index 15001.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle c03c06f106ab7558003249538f7c5211d73985010a6a0c7205d57237994cb2a3; original global index 15009.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c094e5f5ae862767f399d74556820fd59d34f702e527b56f49c27c3bc8b59686; original global index 15033.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle c1322cd9e20c8bfc9fa306f19dbd34127c289dc7be3d07994e355bfa499e25cd; original global index 15081.
def localCycle00116 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle c1a141c437423cfe1c2c69999a944b2744c48ff2fb3e7ac6d092bfd2a34cb84c; original global index 15124.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 23 2, .gapUpper 1 5]

-- Original cycle c1ed39c00dddb93e7fd8321ed53489735988d8935d53d657f550f6333f42c8fe; original global index 15142.
def localCycle00118 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle c700228370a85c2cf658991dbaa09533bc9ff4bae370bf86700728c78c7d6758; original global index 15529.
def localCycle00119 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle c717dac9845309cf8864a43963318f76b344b1ab6f932e6688af487219823cb8; original global index 15536.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle cc4d818f0dae112d308ba535f1a2a5783b930761178b6801c3600156d4bbc839; original global index 15967.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Original cycle cc6f116473d392bdc84a9a7c20b294b33fa799d59d3579c3fa08da8574d7c2f7; original global index 15977.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 1, .triangle 18 2, .gapLower 6 2, .corridorLower 3 6, .thetaLower 3]

-- Original cycle cc8ee7ddafbf454fb98275c3561830e69893839b2f46465d729f315112afdc52; original global index 15987.
def localCycle00123 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle d06bdc749c3066cd9d0cdbf7a2ebca26a3a666114c7a73157e5bd4bfc3f1aaa7; original global index 16267.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle d0988ccd531fd91460b41a356389005a76cf810d2fdd03d89de97e8ae865f423; original global index 16279.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle d1569caf0faa0f481ea95b24353f1d1dbf0bcb10e046f0845aa77dd025f2bd03; original global index 16340.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle d2d5b5a86b6496547bda91e905731294690e59fcd7a486b16765e8df961878a7; original global index 16448.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 1 6, .theta 1]
    constant := ![3, 0, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 2, .gapLower 6 3, .corridorLower 1 6]

-- Original cycle d3bf7a5a83ce12e9386d432eaf9a8197e1d16be31b9dee0e616fe6558baf91a2; original global index 16523.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 2, .gapLower 6 4, .triangle 32 1, .gapLower 6 2, .triangle 18 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle d41a3d61e83a4f1f5dbcbd7b050d9448c111f870ccae1ef8c3f71d07c50f3814; original global index 16551.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle d709732a91396d8e72ce50bb7c14eff15a652263717837313b9bdef3d23cb360; original global index 16785.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 0 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle d82718e88e583a90c30d622ab36576e9251471e4ecdd11402f395c830d0afc5d; original global index 16873.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle d914d95a7797698f191af999e224a05ab8f764288488ecdbecf5c1d4ffa63ac7; original global index 16960.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .triangle 18 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle db29bdd286bd23e159e484dae2e61690f156f393503a154fe0cb40313fa02422; original global index 17128.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e06384b1b9d7b0011ce01ac5b5743eb626e62cebea6b338bf799a89b28b52f74; original global index 17541.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle e1982abb9cd9e6ec7ec6eb46bb11ec98bc13cdd8dbbc46dde20df17360a7390b; original global index 17640.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle e2b7ec7e7c68e58f23bebfccd65e58bf399416ee25488cf613980c148461e107; original global index 17731.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 2, .gapLower 6 1, .triangle 29 1, .gapLower 4 0]

-- Original cycle e32273edb5fc5dd0299515389c50c5b78b05c00ada2b846be1217958492beee2; original global index 17765.
def localCycle00137 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle e3af9d2c936c2e3f3978b7a6cfebd585d58be4926185847f1092a12cd95cea71; original global index 17803.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle e50f15740b3a5e6e1fd5309c29e7086541cac9fca500c346f97c136eabdb547c; original global index 17906.
def localCycle00139 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 14 1]

-- Original cycle e63a6e6db79f1fad2a05fd306171eca9ff80d15bd3954927c9fcf8fcb25ceae8; original global index 18015.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle e70e7e5872e73de131c349d8c0462fce76e4be13b393bc5103e5e533d7d6b552; original global index 18075.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 1, .gapLower 4 0]

-- Original cycle e912bf83f04c461a0044fab162a2642f4ad844223f0642cff36f0db158dcd7bc; original global index 18216.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle ec0fef1f90d6125f6c488a585c3b3443de3ad4f07c6931b6360b3dfb2566e7f7; original global index 18424.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle efdea804b7a9e8b878e2d5b89386bfeb2c4c96ab7aeda15848e7d94a6ff2618c; original global index 18716.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 29 2, .gapLower 6 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle f023a76b3c7a59c93bafc53291021f15e6622b1eabb096e5f8b06d7526918f81; original global index 18732.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f32049f01155891a20903c154770e60c307610682d60367cb789b66a3483baa5; original global index 18954.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6, .thetaNext 2]

-- Original cycle f354355ed977b24ad800eb0ab921c06c23f0d512e42cf5796077940ae095cb7d; original global index 18978.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f54ecafffc78f8c1e4d2ec81773ff46cf19af1c75d0b07bfa044fc12f831af12; original global index 19120.
def localCycle00148 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle f58e250fbc1db7cf1d41a0a9c79be1dc6e57b1af879b767306f5505a2f053b5c; original global index 19146.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f58f6f1a81666d466abadbffb313a5b587cfbc69e2c2d4f6262ceabed082ef9f; original global index 19147.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 2, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle fb1bd243134e6edd812288eb719db1af586e970841c1fe32faeaafac1fdd835c; original global index 19600.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fff288ed1416380be436ac5ca655f124294af624097656157e6762c96b55c8de; original global index 20020.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

def library : Library := fun id => if id < 77 then (if id < 38 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 28 then (if id < 23 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))))) else (if id < 33 then (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))))) else (if id < 57 then (if id < 47 then (if id < 42 then (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))) else (if id < 52 then (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))))) else (if id < 67 then (if id < 62 then (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))))) else (if id < 72 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))))))) else (if id < 115 then (if id < 96 then (if id < 86 then (if id < 81 then (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))))) else (if id < 91 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))))) else (if id < 105 then (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))) else (if id < 110 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))))) else (if id < 134 then (if id < 124 then (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))))) else (if id < 129 then (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))) else (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))))) else (if id < 144 then (if id < 139 then (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)))) else (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 149 then (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 120 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22144)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 133 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22145)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 4, 6, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 73 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22146)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 6, 0], ![5, 2, 1, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 76 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22147)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 20 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22148)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 77 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22149)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 18 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22150)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 6 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22151)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 129 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22152)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 8 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22153)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 32 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22154)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 29 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22155)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 97 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22156)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 29 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22157)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 121 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22158)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .low6 (![51, 53, 7, 68, 4, 25, 152, 43, 91, 42, 132, 58, 138, 71, 130, 104, 58, 38, 24, 22, 58, 144, 16, 58, 105, 139, 72, 58]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22159)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 6 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22160)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 1 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22161)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 39 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22162)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 106 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22163)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 15 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22164)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 44 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22165)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 23 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22166)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 90 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22167)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 44 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22168)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 89 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22169)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 45 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22170)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 110 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22171)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .low6 (![98, 149, 19, 111, 118, 85, 101, 57, 96, 54, 26, 0, 63, 136, 54, 26, 55, 55, 54, 128, 102, 102, 36, 116, 116, 113, 87, 33]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22172)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22173)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22174)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 117 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22175)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 135 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22176)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 150 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22177)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 135 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22178)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 150 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22179)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 48 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22180)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 69 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22181)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 94 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22182)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 131 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22183)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 94 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22184)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 44 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22185)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22186)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 148 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22187)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 135 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22188)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 3 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22189)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 75 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22190)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 70 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22191)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 99 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22192)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 62 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22193)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 40 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22194)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 78 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22195)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22196)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 88 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22197)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 5, 1, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 48 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22198)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22199)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 84 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22200)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 131 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22201)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 84 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22202)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 44 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22203)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 103 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22204)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 103 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22205)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 74 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22206)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 4, 6, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 35 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22207)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 35 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22208)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 100 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22209)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 6, 0], ![5, 2, 1, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 125 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22210)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22211)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22212)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22213)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 81 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22214)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 59 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22215)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 65 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22216)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 65 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22217)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 60 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22218)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 109 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22219)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 74 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22220)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 35 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22221)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 100 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22222)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 145 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22223)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 39 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22224)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 124 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22225)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 79 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22226)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 34 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22227)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 5 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22228)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 44 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22229)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 6, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 5 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22230)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .low6 (![31, 123, 13, 127, 37, 85, 152, 93, 52, 14, 107, 47, 114, 21, 10, 2, 119, 119, 146, 108, 122, 64, 30, 9, 17, 143, 82, 92]) }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22231)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 6 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22232)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 112 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22233)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 126 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22234)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 4, 0], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 50 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22235)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 145 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22236)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 6, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 145 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22237)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 6, 3, 4, 1, 0], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 153 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22238)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 95 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22239)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 41 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22240)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 3, 0], ![1, 2, 5, 4, 3, 0]], proof := .tail 12 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22241)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 2, 4, 3, 0]], proof := .tail 28 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22242)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 151 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22243)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 141 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22244)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 147 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22245)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 27 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22246)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22247)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 11 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22248)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22249)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 134 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22250)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 115 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22251)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 80 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22252)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 41 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22253)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 95 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22254)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 41 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22255)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 49 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22256)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 137 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22257)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 56 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22258)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 141 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22259)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 147 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22260)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22261)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 86 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22262)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 67 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22263)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 134 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22264)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 5, 4, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 115 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22265)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 142 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22266)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 142 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22267)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 83 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22268)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 140 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22269)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22270)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 61 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22271)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (22144 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 22144 ≤ id.val) (hhigh : id.val < 22272) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 22144)) = true := by
  let j : Fin 128 := ⟨id.val - 22144, by omega⟩
  have hsum : 22144 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (22144 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard173
