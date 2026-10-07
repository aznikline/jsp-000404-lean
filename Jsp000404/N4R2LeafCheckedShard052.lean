import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard052
open N4R2RowDataReplay

-- Original cycle 01706140c2dd5ff0df80f413f3f40855faa60042af51c9518164b747a6cca4df; original global index 118.
def localCycle00000 : Cycle where
  length := 14
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 042884d5f59ef95284e265f760327336a46cb91f29f97d6cf532b75e6967a909; original global index 327.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 04cc2a4ae3693dfda3f1664e9488893f60c5d17b986b096a055727afbd270ab2; original global index 387.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 11 1, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00003 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 07e369a4686363be50bdb643a1600ca7d851779e49b58b0a96daf216cc63080c; original global index 640.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 0e0198e7f9c6028baff742f8dec8c8178e0dd2f1e25ad33605c15979fc0db4d6; original global index 1101.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 1 2, .gapLower 0 3, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 11a79be6d8964ed56e80bbceb9d4eb97704268152e05fc9e2e20e93f5bac261d; original global index 1409.
def localCycle00006 : Cycle where
  length := 16
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, -1, 3, 0, -1, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .gapLower 0 2, .triangle 13 1, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 12f72cc6d30097e191014f8363477bf290f02c4152941b30b8719cc28cd8d6ed; original global index 1496.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1386c3febf39743632dd7c0f2466280fe25deede2f2cb631d7164a270c3bddad; original global index 1538.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, -1, 0, -1, 0, -1, 3, -1, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 2 1, .gapLower 0 0]

-- Original cycle 14bc497eff1729289a3cabdcccbcb3a4398097195d812f69b6439ee5770ed1d6; original global index 1643.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 159eb99c0556854d838cfa1afea79ddc0b2658ac7d7211cb6009562819a1983d; original global index 1714.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .corridorLower 2 3]

-- Original cycle 15bc8a0f7da1708da645fef8eeaa73c243136a8e7e4e43714671e267381468d5; original global index 1727.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 18b5feba522a36df0ca1e1594d56a86e7ed87e3526c0f21007f73e4954c30fb6; original global index 1932.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 1a99d4b966fdff1e815556a43b763ef3372fb9ce6fe251b6803c00b4deb4a428; original global index 2069.
def localCycle00013 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 1bf8376067aedf805e94e82eb7b9d010d0fd55c368dbfa859617ebcbed59f5b8; original global index 2160.
def localCycle00014 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1c0dc5269957f686b6005b92f3d3abe9a41b4425565fd8382e458909f4763ecc; original global index 2165.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 8 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 1ca741a218c499bfec6300206c096910f1b3d25ac3d1e6b7e6ff2717df2d6737; original global index 2207.
def localCycle00016 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .gapLower 0 4, .corridorLower 0 3]

-- Original cycle 1d06efaebd49b765f7c93e2857f11dbf752a7c2c91c5dd81cd79695db0319ac7; original global index 2237.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1e004c368782c7dd884e069667bd53293a834f7850f863ebe5c78ea9dcaf5656; original global index 2306.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1f80d2751f5cbfd634304030006186784b5e36e2ffbee0766ae53c866596b416; original global index 2420.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 20937cea40fe169ca5c940b440d4791e2215221f1625f3e94a8bce0d750ca7ea; original global index 2499.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 22a1e6a37c821ac1d935977f75aaaa45b5ec5fd172875baf60fb613ccbabd9a3; original global index 2652.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 2, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2313372d7319241d59e220de4ed2da4eb80b3d06e2a9a848073adfa0973a7f85; original global index 2691.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 235cde56a344649087d01b1f147a974500e18e0e56ec5c5ec443fa424dfc8fea; original global index 2709.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 25512b7d655d3d078c405dba0c63b578338f8e2e4c732f895a798440bf680d13; original global index 2868.
def localCycle00024 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 2757465eb1752ebf1027ac354784b95757eab10304f61656aa5443ccc3856bae; original global index 3013.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 3 3, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 282290055e83768b684a96737117ddf6399794112e321db4cdaf4bfad8cabbee; original global index 3068.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 11 0, .gapLower 0 3, .triangle 12 1, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2825c3c6d9571bd01c5f26f4ac7c64dce47f35c3edf8ef1239a8e1b1c7c273a0; original global index 3070.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 28b83efdd499e70f82ac8e9d3d83df4ba4cb0d05f3792540bf279b7039e98d57; original global index 3116.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 29a9d9132bec99606111fe730c0badd1c79d51c779c5c7da452adc4edd99d111; original global index 3180.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2afb47f6661ad73dc5cd7e1cd3bc87a75df6545231b0d4e6f6afdb56ff68d45e; original global index 3278.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 2df4b9c427fb748d91139583e6659c50c76e84c4b9ef3119670d3f6cfdfad00e; original global index 3509.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 31b54726d31159a93388da1d17004e021c9c719ee3887ed94930ecb70fbf56a4; original global index 3795.
def localCycle00032 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 5 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3414eb90576984ff11aa9b321096d95cf7a643da552a5c45dfd780adbbb0244b; original global index 3992.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 34362967c3a28383fa6a6ff76ead39386835e57175c1136fe71a6058b0ce1ef7; original global index 4001.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 36748a96d879b8e1a1cdb41f4fadd70f0be6c6564d1962271ebced3556a33269; original global index 4182.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .triangle 13 1, .gapLower 0 1]

-- Original cycle 36e4402b38341b493163c06ace05ff971e4f251dce8cc482dc7e0a1c172601a3; original global index 4216.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 373c895f99ed7410ad572ae1f68f3d26b9b3910f8d3a9c769d122c12d67e15b2; original global index 4242.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 38533defcc92ba3e9f6b39a0422834a260ef2b8a3fc2cb3c1928d5e28baf79a9; original global index 4327.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00040 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 398e2c3043010d5288e21d08e3b655cc3b81ed23d24222e7c1d876434403bac1; original global index 4434.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3b243eeb337f3bc4b2641617c6d79fb4eeea6ab41e6e9d369d6d91fb010fa969; original global index 4571.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 1, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 3b425f650a7dd12569e756c4918f0661155f08cb874f4fe61986cc0756277691; original global index 4579.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 4, .theta 0]
    constant := ![2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 10 1, .triangle 11 2, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle 3be8aee696bf82cb5785176f9a1b72af4be0031df4bf6860536108d14f0e8296; original global index 4642.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 3f38e57884729131554e00d86704032084a832f9207d9edc7a6673530a8e2932; original global index 4882.
def localCycle00045 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .gapLower 0 2]

-- Original cycle 401eae5d61a31ed16b3a6a992998f7b1b906bd9ea2fea42a6b33898d3b4b6dc2; original global index 4947.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4291e844516aae08c5893e8ea0cf0668039b46e6ffa7f73773475d8e89f58e68; original global index 5129.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 43e076e88b2b70ba8f285a82ee6afb4a639615690194171f1fe8324efcbf037a; original global index 5254.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 44d9aab1de6b8cb9c44e9979d0d3b2c80f36b0840710dff2b97b763d814cc46e; original global index 5334.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48cdbf9da146262244058d52419d4f6f1df85a3d8379b32b28a5712d7fb311f5; original global index 5640.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 4916241f43b3e2110c27b354a8e4c9306cd795f98860beb5541c327fb0fb7f2e; original global index 5659.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 4925a2b024ed666e8fae323cc6ad3450d698fadf07060e5b87849b29c70a1643; original global index 5665.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 494e84be40a07188280a4394084ae8ec3fb159f39c8d57d7b9fdd644f527c49a; original global index 5681.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 4a373a4c2889d846287b363f8f6f788ccce42dbafd8d13da1085dc773591f051; original global index 5754.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4a8766b17cb31b6bbd268b58c450a6de7c93beccc760897acf4ce96163715d27; original global index 5781.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 4aabe00a10f185a4d83b6b451bcc344a8c267c83fe8a247dc533971bd5634e89; original global index 5789.
def localCycle00057 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .gapLower 0 3, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 4b5ca96af27c3ec799f74ba3282d6a615d5fd059e292286518a3d78e6e206290; original global index 5838.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4e66582ecbf9e5ce135a88e33f8a82dc6cfa8b79155d3e4bf853eae28363d9f4; original global index 6087.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4ee51112bcae6f45a5f6fa24b5807ae754206786235dbbdad6aea87354aa6d52; original global index 6129.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 50a07d176b7fbcf1c3cd211f34afc544f6eb3b5ff2a0a3930157681970d088d1; original global index 6259.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 513f0eb7a92de791d94a1667968b2a75cb250b32cf8684fcc8e11cd0c2574e45; original global index 6316.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 51f9622b4e48e220be2e0a2b12d4d549e141e142f4e114abfc37c44a3a2bdf2e; original global index 6375.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 52a51228a3cc70a24c8903a8ac92188529eea9ed4c127d7a211b118bf0083ce9; original global index 6422.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 1, .triangle 11 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 55bb80703b0de4e7d5a245193e9005c5c12a1f1e247350be2462a885332d9eb3; original global index 6649.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 56394b3de2e97dc70b3436b7c221696b186fb1274f98c1e3ab969547dc9584cc; original global index 6686.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 56d1463b1af6bc07120582b6b6db50f7f2345fe6ed7a76053a0a8cc5729abe41; original global index 6728.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 57a04ac04014d9cb9db6d5947fa362450fdd81226dba13cb72793c8591f47b78; original global index 6801.
def localCycle00068 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 57adcd5b2f6a526ead984fc82264c298a768ba409099847448869b7509d7b551; original global index 6805.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 59dbad3ddaaca14ace92a97340f97999adfbb61f5c24d50c3fb48fb0ce7549c5; original global index 6990.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5a733b6d40ecfd92233e85b82fdb1323f45bfbd81cfbed29000798bea86c64c3; original global index 7042.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5aaeb24ed140e2446520911979df00da472b3135d59122ac72140c76031444ce; original global index 7060.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5ae8d7fd8290859c4389adad36a0f8ed33c654b4445fc92fc5e0023816601f67; original global index 7077.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 5ba46fac8afd52124dd095bb56c94b3ca5ce78518ee94dc60dcaa0a7434ecc0f; original global index 7125.
def localCycle00074 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 3, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 6 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 5be7fbda656183eae6af4d802ca752c118f27a412a304c8d6549eba4be56e96b; original global index 7147.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5c298ab48add7a660ef9bec979cc2df0ca4f19deb8f49741b1ed2652aa7afc90; original global index 7176.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 5d085b21a81f09f6aeec16f4fa7cf362f5513b1f8974fa35f7fa18003903382d; original global index 7238.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5dcf7252ead96684b01e464c80fd4ee7ca6000f2d8b3f2ee89afe5fda444e6b5; original global index 7296.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 5f91c9860dddd77866014dcacbf72d2a5b7c444119c38d3f8fffb6370b833f86; original global index 7443.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 5fb85e8cd157f8bc431dd807e0b182282e773ed9c9263795912f0ef25166b90f; original global index 7456.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .gapLower 0 3, .triangle 13 1, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 5fe6fa77ce3670e737cd1ab00e207f42c4036075a16146a4be7d7286a47f4351; original global index 7475.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 61528c016ca006438fd800b2c23839fc840d920dff2ea14a68b85f0d8e34115f; original global index 7589.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle 61cf2aad60066130d311e5599cb05d6afe19f7594c6ffd4f018b4117c259a3bb; original global index 7633.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 7 1, .gapUpper 2 4]

-- Original cycle 61dd9cb898ef6545d7b45abe41724af672b4899c48bba786aaf1cf3083d4b07b; original global index 7639.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 10 1, .gapLower 0 3, .triangle 13 1, .triangle 2 1, .corridorLower 0 1]

-- Original cycle 62512a918fa0d609fa75bce46b8efbf3d06af99c46f335fd619e3561c3bc9ac4; original global index 7674.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 10 1, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 62518665f674fca4d24a9f8140a28c1162d4ec6eff8c2332b9b9509167319cd9; original global index 7675.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 636f84b0873cf9f5d6432c8913509c4a22f354dd7518617816e14fe32caf6f4a; original global index 7760.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 63de5a11dba230216e081a8ae73093cf1e648fc37fba31d5a7722c42be03be2c; original global index 7783.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 642897f8aaad649a0aebeeaf47dc35cf4a079f0e14518110905e5bc95fa653fb; original global index 7804.
def localCycle00089 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 65fea67d01f7780b3403e22f83ae1d7e7cd59321473f2f059475b00834b24c70; original global index 7937.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 2 4]

-- Original cycle 66d80a23dff38efaa103aabecef93834d3b68bd32c648faba4ca8047d9a66fef; original global index 7990.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 67335d407e25d404fc8d983c9f88f5df36d66f094e37cffa7a5525acbb9bd1d1; original global index 8022.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 67b5e0717d6fdc3b3887247fdaf1437e9782f296f3be349f81cbbe904c42a3c1; original global index 8055.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 68967f88e7400bec3120e8687f0c28caa79e20744c416a89c236ed13726a0676; original global index 8136.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 2, .gapLower 6 2, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 69504cd1442bda2858299dd5a13908d0321cf68a6b2ed98699d6847190cbe368; original global index 8191.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .triangle 9 2, .gapLower 0 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 6c40ea3ded0fa832a48355c31eeb665eaf69b64ec5d75bf752791a2229597a85; original global index 8435.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6e52cad9f87c5a4af79598cd8014743ce82abe0defc7d9d59ba194bc8b8c6d90; original global index 8562.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 6f8026dcb3e8ea84a89f016db3233e1f89d9664fe0b99243a3300f6445291a21; original global index 8649.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6fb7cdd5d699ecab49e512c6c2327b41fcb91c25f401b37fda6a8fad5cdb4983; original global index 8667.
def localCycle00099 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 21 1]

-- Original cycle 7010d86bb9f97f960adf547ad7faf5fe0a1f6e7614f7b2e44c61f1bd8b5a3ca6; original global index 8688.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 70dc4c64dcd8345c12e74689eae12b91dc360652e4ad06243ee8a828625da85d; original global index 8745.
def localCycle00101 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 715f8e8e3f24b4483af6acd7a34b3f5aad4f73cf943a3d7ab4ca4219ec6eae4d; original global index 8795.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 71b4a8d96bab90875efbe529f1dc9bbabd5883233fb235825c33ff21ec4a93b6; original global index 8822.
def localCycle00103 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 5, .distance 0 3]
    constant := ![0, -1, 0, 2, 2, -3]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false] }
  origin := ![.triangle 5 1, .triangle 27 0, .triangle 33 1, .gapUpper 5 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle 7473247d60ee6478eb7b953802919453f8d3aa7287e97c700985c0c90950cdbf; original global index 9029.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7557ae8b1ed6ca9b733591eb6b91f1dc923f0d0212521959629d35ddbde4ea34; original global index 9090.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 1, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 757225d02f268e8a7e77bf6abf96f987b75923ff05323887fe6dab3b619ae210; original global index 9100.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 76968299c805b121261a4dadb734635e7ae0b68aebea36d1379d5920df1b5127; original global index 9178.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0]
    constant := ![2, -2, 0, 0, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 5 2, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4]

-- Original cycle 76f1928b3cd40d9e4d06dc93842e9edd88218e9f691a78eea3b80a3787ab2103; original global index 9205.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 7751c6589873fd9d7c065e828afeab8f3a592e56214407bdf21b592fa12f0c1c; original global index 9233.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 77dc09383c44ed4708ea85bf22fbd8775294957428476964d7a6070700743499; original global index 9268.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 788b755a2698afb4dffff1edd4028bff209bb0122c2bc6949413693a1a8febc2; original global index 9326.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7acec9894961ccc8dee829623406f4c62d94655a0d0823428fdca99e4fa5667e; original global index 9507.
def localCycle00112 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 7b50d10d56c321e2ca2366ba368e70b24be5baedba5ef8d2b1e43e666b226076; original global index 9550.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7d8bbbb3d01520fe9460a40cf98ac0d5b73f869194db8d4442a6a29e424e0b76; original global index 9744.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -2, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 819041bc8a1d251e602d24f2ff6c1cd355e37f8353302d2bb25a49f479a1ce6c; original global index 10062.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 81fdf9bc1dc5d16da738c4c0164da70ef51776d457bf07e9aeebaa41439a23f7; original global index 10093.
def localCycle00116 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle 87c61a7c371df3d9332fae0a15bad0a25820c12831ddbf40dd0a8705bd3d8282; original global index 10522.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 89b059826cf1bef92ad9bd8114a149c630d0ed88aa7e6da2e1ef81c0bcc91c89; original global index 10667.
def localCycle00118 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle 8a3ad827b337fd64830f45eba7d20907fc7c2f47a79e49e87c2cc3cd51afbc07; original global index 10714.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 8b3ca189173aa1e048750a8690914fa735f0c488559cb8378c1195630411444f; original global index 10787.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8b41b5173eacc0a3693415123b4bf2d0b176ded7fd9c997a0ef34b8b50257e98; original global index 10792.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8b6cdc580d9f2e0760583179f59581a02e48be74a9570b1795e8800e98f51290; original global index 10804.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 21 2, .triangle 24 1]

-- Original cycle 8b9e06fe5e03e1bed936bb0a0e9a149690cb5f61f922e7e5c84aad041284cb51; original global index 10811.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 8c03fa5e7a9e1040d0e9038e9af5cbfffe6d0c40a4d4f7435c13c2f6d64e99d4; original global index 10839.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 8d6ce3d5e620b38a9ca4b1fb4ec608bad4e5bebdc6108396c75db9bff408a701; original global index 10934.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 8dafe81d24aa4b058238605e25123861851a1185416b1dd7d89cdb9ace227121; original global index 10960.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8f0808433f5f402635c65b9fed02f2028a3afaa144c44da78a2d11442000866a; original global index 11066.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 8fac0e5cbafdd6555a716fc212d2671221b203daa970812b10a00cbc106d8fec; original global index 11120.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -3, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8fb493f85c35829cf07aef94c1dfbe8af11e65a4bb496bd4d392022e5706df92; original global index 11122.
def localCycle00129 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 23 1, .triangle 13 0, .gapLower 0 1]

-- Original cycle 908caa5bb91fac55a0d0fc60310ec0db863f769c8ee021cd71360453edc5cd47; original global index 11190.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 3 3, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 923d8e614c29f7bd458d9a3344826f1910d949ff3a4d395a3fe7197fa076d0a6; original global index 11325.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 928a672a66a4cea977a2fcd38fe221d5bed65e70253946dc5053b7a98debb241; original global index 11353.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 92a54779d99aa4ee0fb81cde4c6d74f7c8fbd92dce4066a2ad10017823a009c0; original global index 11361.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 9419512e40ee3cd94215d8d215ad1f1fd16f9717a41501b45a392b9689b4eef3; original global index 11488.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -3, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 10 0, .gapLower 0 3, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 945d0205e70510d3379577fae952cdaecd4a0a96536aa8d11896d6253f8195c2; original global index 11514.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 946f980ff79a407d60e0d44b277522275af3f176c69f7f2670f35daf36ea90da; original global index 11519.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 94b60162e02a72c89f4706ad5d83f5765312d07544bd79251c6ea23197121dd6; original global index 11540.
def localCycle00137 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 94d9625196e53ae9f6d9aac438548de824afe02f7df24c6743db29b09fbd809a; original global index 11556.
def localCycle00138 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .triangle 5 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 950750e3b0ae3fa53aeb72f6793269fd5e308a37250330a84b93c21c85788926; original global index 11571.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 953e8c21043e6a5d896c9dabb8399b4b7eeb46af07fa031725fa48c84fe02edb; original global index 11594.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 9560d73d43e7afd3a2a6442e716ad1098f1eabb9d50451b8b004ba8f87697839; original global index 11610.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 95df984def8d178d73923f0ca27f0d54bdb0486c3fdbc689b438ff280c06aca0; original global index 11650.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 27 2, .gapLower 6 2, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 963e25d90b511295c97a52fcea7f36414ae265e63122323fbce32bef99bb8afe; original global index 11681.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00144 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 996602a662d1a4ca0153d6dad9c0544c1b95ae0bd8061fc97ee731f45c9890cf; original global index 11912.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 9a28a678db644588907a7a01cd90dfbc4bcfa9d02c544c56a6c1f8f239258ce2; original global index 11974.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9d485d9dc55734448bba2cad3aea803c1e91da0b983f94324d38b908812a205e; original global index 12235.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9eba5418cc8d6516ad2176b292db0187c1b702c750bf56623ebc25bc97c8ad05; original global index 12357.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9ee37949dc6ba57b947f27724eca8790a719b8f5250325ac17937edb7a486150; original global index 12368.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .gapLower 0 3, .gapLower 0 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle a0a5b61cc038c435672ab1a59a5cd94e228a3d18e542440679cb4a08d1c35025; original global index 12496.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle a13e91047d95e2c116bf1ce5760ab0ff34b374d2c598d990981abfa14678993f; original global index 12537.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a1713a90c6e8f795fb72a42fae81bcb22a8a0d43ad14697ab14d7a415acb5058; original global index 12553.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![4, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4]

-- Original cycle a3ab91cd18f5292cd0abf6d1c7612e3f4ac945cff10e3a5cdf0aa2ffe9a7c89b; original global index 12725.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a3bbfec6f5fa126437582c6080c894e0fd29986a7ade080470eb48c979671a43; original global index 12732.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle a42978e5a92bf07b2e8e3b88496e9b3c809c904f0ad290702a61fe6df965926f; original global index 12761.
def localCycle00156 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle a45047d47c8599c8b8766560c83db66c62f5ed32a24ded64e5746f12129f0437; original global index 12772.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 3 3, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a5f69f497091128eebf0741176d6ff11b6e23db590109ab6b968d1bbd3df87c1; original global index 12897.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a77812e67e5a7f07e1ae552f2a6c645834dbf945e86812ae47cbe273c8232e4b; original global index 13027.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 6 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a7f95da4608cccb2b212304880ccb43f8b2fdedf821058ee2402a09c13eaffc1; original global index 13076.
def localCycle00160 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 2, .triangle 13 1, .gapUpper 4 3]

-- Original cycle a9b33030286cdfc6f0153fbe6fe23dcada307c8cdc8fb4f4488d70023b48d47e; original global index 13210.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle aa536b7c1d1cd53107e38d3a51c0001f4c5ce8b08eaf8beb97d7a7ea7e9119f8; original global index 13263.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ad0cfa8abee62ab6559434fa2e77dc6e6497888f76ffd5ea46160dba22ccc91d; original global index 13491.
def localCycle00163 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b3d184b9b114f0c7b9e24f726147a38a0cc8686910c0637c14f60200596197d6; original global index 14043.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b45cd37a3249b13c485f82f2b98c634331fadfddc3abfc522905a27a8d84f878; original global index 14091.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle b4f30d28fc88f418708fc6a1266771d70225bb434e33a6f8839060743a42f1ec; original global index 14134.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b6499f3cffca17d32c184df7022efe67e8ff7fe4e387976982a29c5fa5490336; original global index 14245.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .triangle 27 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b716edb1ac6711959fde3efddfa924d79e2a41cd4b549b556ba29ff72abc4721; original global index 14299.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle b76ebf9fb0d46428e98504b422b471dd870c8255d6fc0e9f1c582c08d92f5b0b; original global index 14317.
def localCycle00169 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle bbf899eb4d2b2fed99c4cc7cba5c42a939f60fc769dc1304a610f61479ac15e9; original global index 14680.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .triangle 10 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle bf487b14d785df9360f5a569239f6c0b804d1a1f3109fc27f19dcfd774941d64; original global index 14929.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .triangle 11 1, .gapLower 0 3, .triangle 12 1, .triangle 2 1, .corridorLower 0 1]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c0632bc111450dded335a294c87cb3840f99792053c84d3363a291ac017e9202; original global index 15017.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle c06396193593f8957ee78580a25fa7cc711f71452351561cd82c6f023e1be072; original global index 15018.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c224bbfa7ce913ea2b5491364a1c519577daff191ddc4982b5985a0f743300e2; original global index 15158.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 0, .triangle 26 1, .triangle 27 2, .triangle 29 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00177 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c362517fc8da9c757901e950c265a553902cf6b99a3967293680556318d84cb5; original global index 15244.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c3cf799de89ad06e34ad7a8e2755f07ea32fc55dbd200f3110e4bf8071ca27c6; original global index 15276.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 7 2, .gapLower 0 4, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle c65a12ba24578998efc665a123ce9d052847cc6abfadb30d55be3a03578fb5f2; original global index 15472.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .triangle 11 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle c67cc9c5b8fd86135e7b82b5be2446c0e22eb5eadc14267715c97cbd37a24c8b; original global index 15480.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c94dd3d37e3fc33a9acb62f638f548e91dde3417d1d02e43b6269319effe9636; original global index 15737.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle cbff6bdf43a48bd0e5e91b9183f7d08cdef73ed5fdbfafe6ba480aba11a833cf; original global index 15942.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle cdfda830cda984cbabb49fa48c03544c125e4f3a20ae03bc56fb7380f564315d; original global index 16091.
def localCycle00184 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 1]

-- Original cycle d035e7288cb2d42d8b29e4d80def6d1db36c4e3d84278eadc08c4573ea5d65e9; original global index 16253.
def localCycle00185 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d3b665fd249f507e3e2fac4628366ce4a6da943fc6d3ae50c0d8f4cbe990617e; original global index 16522.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d414d0d172394c295a57a6e916df95139967b77d3ff95174b273a4e1a0c3e65c; original global index 16550.
def localCycle00187 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 26 1]

-- Original cycle d91242d1024f4bc7bb231a7bbb5307a38ed7098533f91d503dc751e3d3f01d8e; original global index 16958.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d93fd1a4acabc1189dd4df87f129a81a8bec39ba7239c6e5a821e9d92c7bb39c; original global index 16974.
def localCycle00189 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d973ddcb76ff230dd9fd3ba7c7f33960df11fa8424bb54625a5dc4c32dee885c; original global index 16995.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 3, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .gapLower 3 3, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle d9eb114dcf1d46c59f3080394545cea0eb7e67b3ba133da10dcc697b53073ad0; original global index 17024.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 14 0, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Original cycle dbb7b81d4effc793858cd9e0051015814b03f301c8e1a15e979b4576d6481e8a; original global index 17171.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 4, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle dc563c98f206da8d17088ba849e70023493fb24adb115b60ac80ac0315709d50; original global index 17219.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle dfe29c603dae67e669cd9a7132d7975dddb8147e4f221d4f5f103d697199ceaa; original global index 17496.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e0ae0b2f76484472628d88e20f897bc3713c5a0cfc67c77cc8d120c5574b7ff8; original global index 17568.
def localCycle00195 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle e21366dbc392cc4d18ce0434922eb39aaff39f57b673cfe88272a40c395f7053; original global index 17679.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00197 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e4ef5978ac14ba605bdf7bd2295863db34cecdbf0956cba28bcd2c061637b52a; original global index 17899.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e56a0073ba0224bc7b3b4995e0af304e3d210a2cced13af9ed84f855df8adfe9; original global index 17937.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .gapLower 0 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e6cd5262e0304fb8a3ed1413119fcb7104f5a1f685d71def63e7a5d363100578; original global index 18056.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle e961d3d178ebaa042b6a46bbadcc3b66c1a86baf2de6c01d6da3bd0491889047; original global index 18239.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ea0781fb605d308182422247566cac8de690a4db14c079bc9e18838501ace7a8; original global index 18282.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ebd0cc451416defffe07b6b194c4e174541b1159d927886bfa972c236456ec3b; original global index 18400.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle ecc0ee510869bfdfb25d052c1b7ebedb2283bcdfb0d1f64740192efcf64d38cd; original global index 18482.
def localCycle00204 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ecd35a95f9c368331ae202f38def1ec5dfcc48f6d58c54d1d4952627a72e8810; original global index 18486.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 11 1, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle ee64d74f3567e826849823f40e37d59db28578c35529517629ff5e10ce4d5fc0; original global index 18610.
def localCycle00206 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .gapLower 6 3, .triangle 23 1]

-- Original cycle eea5fc96e9cecae64f2fb5df14fd3e7ee1d306e96b894eb2436fa26bccafe7de; original global index 18623.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f1939b6370bccc27ce2fd54707a2f47320ed438a50da2248b9661c6a5f86a028; original global index 18835.
def localCycle00208 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 6, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 7 2, .triangle 10 1, .triangle 11 2, .gapLower 0 1, .corridorLower 0 1]

-- Original cycle f1c1c702990ecd9f0940fe1f4405d6c2975b173522e8a7fc37e73de9662ab8b9; original global index 18853.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f1e1eb37395036a6510e90c4c54f3383e2c293e245e42053a16e3c38d32d3367; original global index 18861.
def localCycle00210 : Cycle where
  length := 16
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f373a5dd914491bf0ef1423b5b0ff5421e06e18fd348d9068584f9350b048998; original global index 18991.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .gapLower 0 4, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle f4657372bfeadf64919563758a6ab14f2a4c4e542ab96fd8a1f1f3cdd4e0db9c; original global index 19052.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaNext 2]

-- Original cycle f517b448ba01e71a725e8ed4d0b494dac64f086e08c976625fbb8e0ad6a5eef4; original global index 19106.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f5fde4dc325f536e98659c19f3ad48a571f4d605b804231a5173484769ada4f2; original global index 19194.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f68841377351eb248c18f31fcb434088178dacc70c651d7d37cf512df870926d; original global index 19233.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 12 1, .gapLower 0 2, .triangle 13 1, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f828d029c09acc967ab9df3266bb2a663d9644b2f5fb0a7bf9a6e6cddeb9a589; original global index 19351.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .gapLower 4 0]

-- Original cycle f85edeb6f10852a619c52e432f11249fd445c6f653ee83fa13aefa0cf6da7e03; original global index 19370.
def localCycle00217 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle fa475957f588ba08ea0a6368b1d1853f1fd1fca52f0f2808d5e72fb0f578d9a3; original global index 19521.
def localCycle00218 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 24 1]

-- Original cycle faeaa8f064594c701edc6c8ec6e1d8c3b10ff68d9a575e574cbc88df121745d7; original global index 19582.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle fbfe2f244af7d302b0b317ca7df5cfa2cedb91a91df010af445400e2610dcd47; original global index 19674.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fcb5b03602a11002fbe7dab23c2f58871d815912932349bc77ef1d2e4b2f0885; original global index 19746.
def localCycle00221 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 2 3, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 5 1, .triangle 26 2, .triangle 28 1, .corridorLower 2 4]

-- Original cycle fdb940b2bf4cbde4485861f54d939b754d48aed98571084454921b62363b56c7; original global index 19830.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fdd235577d90d0187ad745b63034e611b6ec571fa7bde3a48604ea19c9ead2f0; original global index 19838.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

def library : Library := fun id => if id < 112 then (if id < 56 then (if id < 28 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 24 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))))) else (if id < 42 then (if id < 35 then (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))) else (if id < 49 then (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))))) else (if id < 84 then (if id < 70 then (if id < 63 then (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))))) else (if id < 77 then (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 98 then (if id < 91 then (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))))) else (if id < 105 then (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))))))) else (if id < 168 then (if id < 140 then (if id < 126 then (if id < 119 then (if id < 115 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))) else (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))) else (if id < 133 then (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 136 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))))) else (if id < 154 then (if id < 147 then (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))))) else (if id < 161 then (if id < 157 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))))) else (if id < 196 then (if id < 182 then (if id < 175 then (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)))) else (if id < 178 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))) else (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))))) else (if id < 189 then (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))))) else (if id < 210 then (if id < 203 then (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))) else (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))))) else (if id < 217 then (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 104 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6656)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 14 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6657)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 89 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6658)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 210 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6659)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 0, 1, 4]], proof := .low6 (![50, 53, 142, 109, 31, 177, 39, 75, 21, 98, 18, 81, 81, 151, 167, 54, 69, 69, 79, 48, 145, 94, 174, 111, 146, 52, 168, 126]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6660)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 0, 4, 1]], proof := .low0 (![91, 35, 45, 133, 103, 90, 176, 222, 27, 80, 138, 83, 8, 189, 129, 129, 129, 129, 78, 180, 64, 43, 199, 105, 84, 157, 16, 107]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6661)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 2, 4, 0, 1]], proof := .low0 (![144, 184, 160, 134, 12, 90, 85, 96, 121, 5, 211, 83, 0, 214, 57, 211, 83, 208, 150, 95, 215, 6, 123, 42, 57, 200, 179, 143]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6662)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 188 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6663)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 187 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6664)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 86 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6665)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 20 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6666)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 148 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6667)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 213 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6668)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 158 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6669)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 135 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6670)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 135 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6671)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 120 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6672)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 163 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6673)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 135 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6674)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 135 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6675)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 120 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6676)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 77 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6677)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 77 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6678)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 77 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6679)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 77 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6680)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 77 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6681)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 77 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6682)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 139 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6683)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 139 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6684)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 6, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 37 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6685)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 131 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6686)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 156 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6687)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6688)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 7 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6689)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 154 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6690)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 22 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6691)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 10 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6692)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![2, 0, 5, 3, 4, 1]], proof := .tail 93 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6693)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 0, 3, 4, 1]], proof := .tail 93 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6694)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 223 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6695)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 141 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6696)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 141 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6697)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 11 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6698)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 141 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6699)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 141 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6700)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 6, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 76 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6701)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 92 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6702)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 193 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6703)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6704)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 44 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6705)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 125 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6706)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 125 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6707)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 73 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6708)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 216 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6709)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 166 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6710)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 213 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6711)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 158 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6712)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 209 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6713)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 1, 6, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 149 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6714)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 1, 6, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 152 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6715)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 4, 1]], proof := .tail 163 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6716)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 4, 1]], proof := .tail 163 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6717)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 6, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 149 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6718)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 6, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 152 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6719)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 4, 0, 1]], proof := .tail 100 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6720)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 0, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 149 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6721)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 152 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6722)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 0, 1, 6, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 71 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6723)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 0, 6, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 71 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6724)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 71 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6725)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6726)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 155 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6727)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6728)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 125 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6729)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 119 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6730)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 23 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6731)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 108 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6732)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 7 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6733)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 154 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6734)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 22 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6735)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 3, 0, 5, 4, 1]], proof := .tail 191 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6736)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 0, 4, 1]], proof := .tail 88 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6737)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 6, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 93 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6738)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 0, 6, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 223 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6739)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 0, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 117 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6740)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 0, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 76 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6741)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 76 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6742)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 0, 6, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 11 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6743)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 76 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6744)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 92 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6745)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 193 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6746)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 182 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6747)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 127 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6748)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 203 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6749)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 38 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6750)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 182 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6751)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6752)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 113 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6753)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 70 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6754)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 22 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6755)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![2, 3, 4, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 207 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6756)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 5, 0, 1], ![2, 3, 6, 4, 0, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 30 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6757)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 5, 0, 1], ![2, 6, 3, 4, 0, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 181 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6758)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 201 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6759)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 19 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6760)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 198 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6761)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 196 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6762)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![202, 3, 115, 99, 33, 40, 1, 49, 140, 170, 32, 212, 161, 147, 153, 137, 9, 159, 82, 2, 194, 41, 29, 186, 55, 13, 197, 173]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6763)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .low0 (![102, 169, 132, 56, 130, 24, 165, 101, 220, 26, 192, 62, 62, 67, 101, 101, 101, 101, 183, 171, 4, 58, 116, 205, 172, 25, 190, 15]) }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6764)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![87, 3, 115, 99, 28, 195, 66, 49, 140, 170, 112, 118, 204, 147, 153, 112, 118, 74, 82, 112, 118, 41, 206, 218, 65, 122, 112, 118]) }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6765)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![185, 3, 128, 99, 28, 195, 47, 49, 219, 170, 112, 118, 68, 147, 153, 112, 118, 36, 114, 112, 118, 124, 206, 218, 217, 122, 112, 118]) }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6766)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6767)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 1, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6768)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 164 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6769)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 164 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6770)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 164 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6771)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 106 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6772)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6773)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 178 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6774)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 46 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6775)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 61 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6776)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 110 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6777)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 162 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6778)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 34 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6779)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 136 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6780)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 51 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6781)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 221 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6782)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 175 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6783)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6656 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6656 ≤ id.val) (hhigh : id.val < 6784) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6656)) = true := by
  let j : Fin 128 := ⟨id.val - 6656, by omega⟩
  have hsum : 6656 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6656 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard052
