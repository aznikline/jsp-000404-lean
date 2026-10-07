import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard050
open N4R2RowDataReplay

-- Original cycle 00bfddc3c15f734f7b4bc19c677f3c3b0675d9f4ce6edcb37a6dea83b01ad75d; original global index 68.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 011bddfc66bb043af1b4167a247d42a0aa56ccc8463f41b306042769b6945751; original global index 99.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 02abec45e8353837749761c6603736dd9aa1295fa559c5bb833192381516fa8f; original global index 209.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle 02f141a14ce4421da9a58a9e51f1add34b87e5a603d1da11292384ec6e77d266; original global index 237.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 058a5d2602e52e39f8fadb1e01b88a00c53e6722d9996a2baba9059f2b62f67f; original global index 452.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00005 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 06cf9950f712a612160bdf709685ec32e6629f724cfab4b64efd3d21ed8468c3; original global index 561.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 09b0b896dd4e431a98501dd35f572f42374d6d841e831a1b3fc7c5e62a0fb530; original global index 773.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0c9d19c811497ade2b23bd084d7fe0c71b4e159fc96da93673ba6da2245c7c95; original global index 997.
def localCycle00008 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 0fa8923caef0d192596b77026af084460ee548e5d15e856d4ac4d1e371559f07; original global index 1248.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 11e50096af3618e06ea239c46801dc6551919ee26be9bc9a94c9db37b0431305; original global index 1431.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 124409b6bb1c39fff3b094970d55f4104b8d528578b795c27bcd24b3ccf76ad1; original global index 1452.
def localCycle00011 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 131f2c152f244b2fbaa869251b6af31a5e9aec296cc29240e22e462f97da1a3f; original global index 1513.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1330f1672e336a58860dfc794db665fc0e9c2f4317fec675ba9bdc64ad752f3c; original global index 1517.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 179f52e9965190cfe345522f6dbda1309f13baed89296e2f38e43e5422cca462; original global index 1844.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 18006f887f697c1209a1296c5d072023261d00d91a008d317c053dc0c0512087; original global index 1874.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 1deb891405ce594e8206dde041685df73def395511604d5cda8d10d261a271a6; original global index 2299.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .triangle 33 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 1e9779630862a134eb28612ba8c610194eb053d51eba8dca6fe5abac071770c5; original global index 2347.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 1f8c7e16ae0cb563fd72b65c01dea80ba0c030402d5371520e8d800124b15cbc; original global index 2425.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 206a030cd40e8a32a89b8371c47b23ad912aa548feb0e67fb40fe63f120df9f7; original global index 2488.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 229d0f8f2fd3577efe3ba40e74bae8f5d8ce00acb3c37cbe66e81963747dc5bb; original global index 2647.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 235cde56a344649087d01b1f147a974500e18e0e56ec5c5ec443fa424dfc8fea; original global index 2709.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 23a770442cc1a3d1f9c93c2ed4dcd917a9c6bfe100d7f5c6aeee6c01f3132d1f; original global index 2732.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 27362dbd7fbc4c3edd56936d97e6ce4a7102d719e6919773fe01938e7558eca7; original global index 3000.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 27bcd3705d084dbf9b732187ce15e3e193811c5baf07080a8bd6b6d6a6b173a8; original global index 3036.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 28b83efdd499e70f82ac8e9d3d83df4ba4cb0d05f3792540bf279b7039e98d57; original global index 3116.
def localCycle00025 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 2a6021c2884720d4d10784e8cfe60a36862186f49863ed36cba9bd1790b3a08c; original global index 3231.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 2b5153c3c117529c1c3f542e5a88bbdb0cf3e42a57f5a76509680168f853d881; original global index 3308.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 2c2aecd04f2b0dc48adb8828a08ac49964f4e7b562508c9b7f1e4344b42e3124; original global index 3379.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2cf89c55736b2a7d842d32875d854f4f6710c9074a55788def7ca7cfa9121f60; original global index 3436.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2ddd4a3a6160d06bb6d106120d7adb360b0ba67572388c19b73ca4392b55fc77; original global index 3502.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .triangle 33 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 2e9d6dd3601f3cdfac85ba407a4c3bce965c32c414ceeffcd02e6b28d2cc2da4; original global index 3561.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 2fa791baaf640f63bbc9cbf8ff2dbbae1f77852331b503bbc88c934b4e0a2e85; original global index 3643.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 325682f47be2a3a1506d68cf8c057bd27cd55dc4df12fb90ef3ca8efa9dba19f; original global index 3848.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 334301369fdcad4a42eab558ee133392b40bf610580bb62ae4165281b5a8bb14; original global index 3922.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 336ee3110085343176be0a2cabc5dd49b631af40ac7e63428f367e5f097d7928; original global index 3936.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, 0, -3, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 378a24ffeaa4fa2bf45d12c51c4e5336e0f2651e299855925d1507224cce00ac; original global index 4271.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00037 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3a1ca81e17b251e7250d9f2c7d5d7ffcb9155e1b4b15cd4848d9bee25a51ae92; original global index 4485.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 3aa6652cce437e53c66283ad1bf40c456e90aaeaf99508bbc9d63392a7d15b60; original global index 4526.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 11 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3bac1a5e0e9447c83898f2f326a32078342a5f8d046262d98cf6b05a57e4fd18; original global index 4615.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3bf47417c78e63d2f3104ed5aef0d108e5974d850d4b98bd572ddb7bdaf52080; original global index 4647.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3c5b8320c012432ecdf21814369dd01d3459a6ca13c924223d8c7e5694b6ab11; original global index 4680.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3c8fc1c0dabe8f4733414dc4a4a3745764182015f41ed0c56df34110bf4b43f2; original global index 4698.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3d420ad70a487e2be149bf76765933716422e5b739cc1f977c822620a9f26144; original global index 4744.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 3e2df6cdfe7bbc0647c20f853faf003f80473c4fa24545df7109ee8406687b21; original global index 4812.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 3fc63d7ba51a08a684f92211372d150ab5028fbf9891eb1f76f306025a8f1396; original global index 4926.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 438818266c0af205e97eac7dc95adfb33349a3b8b488077f947150d73e0f9b3a; original global index 5222.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 44d45f8ee1117b6b7c37d5ba7b8e717d370ad7a22a7a5012a31b609c3d85c154; original global index 5331.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![4, 0, -2, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 4612b04e78c7e3af5964e8c95e447e21a89706ca5b23056089b5d0ccc76e997a; original global index 5422.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 499f7341fe4a402f25b7a45c1bc2d5591017b55dd37fdc9651a58b3ee2b7d2fb; original global index 5712.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 49e0eeccccb39b61bae158744fe651b9615fd556b17bc2540e1b694adc563737; original global index 5731.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4a7cc3bc807662c612aa42a2c33eb252d45a3bf4e3f62e268ceda4ca12df1e2b; original global index 5775.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4aac45f5552cc717a02fadca6d794f578a0725e75be2c83f816b1340cd2daf1e; original global index 5790.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4b783363a1e60a9f48976e79f40b1d365509a219d05058abe16ba15adac40745; original global index 5847.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4c79a012d473683ec434a51aa3a7ed0c0d36bf94c5a9691b1b6bfc53398f978f; original global index 5937.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4f56576fabba06c880d21369bc68cd08fa26652a8788d9d5f74b9fee63968c38; original global index 6166.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00058 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 53b2990f3a308b2f2e8200a2c9dd4c88f67406d20bf05b7f949bf696a41e7e2a; original global index 6502.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 5544c97f9477b1f9378b7f2c91bedeb8f7ee61875d9d0f71d032c616ab3d5498; original global index 6601.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 56d1defef6027de4e8d9a38d4f6044ee855911d96a80cf36051a7ffeb8be88b8; original global index 6729.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5764e5b39162f0fcebdebc283612ebb3aca7d1c0ffaf40162b7d2c39770bf93b; original global index 6777.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 57fadad53140f5834293d259d6697a87566bbe03d01ee2f3ba9252a25b24562a; original global index 6828.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 591699af4042d97949f74b3cc1135c6d2de3bb93cf83ecf8540ed35f2f4f743a; original global index 6909.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 25 0, .gapLower 3 0]

-- Original cycle 595624f1ef7dfe32259da883dad40332f0cb55ca7857accee23b3f6767265e9b; original global index 6938.
def localCycle00065 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 59b2967264f901cc1d6f865b132f82919ffc7c7efd2df32f9f105a35a54974b5; original global index 6979.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 30 1]

-- Original cycle 5a8387e98a9aebe5bc90977af75da11ac613147c3fa535f839ea14d3a86354a5; original global index 7047.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 5d3343cad1e0b85eb1219e680e29fec15f42c0e9fc9799b7c120279792a53a72; original global index 7254.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5ebb9322478b33dac49cc28b60ab48517ce15660b75cce1507cdaa44f3a8ac61; original global index 7372.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 5ec07883f456e462c93da0f9b065e4dba08e000acdfa37afad88671f9f4a7bd5; original global index 7376.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 609cb687f53a157afe1f858b91f42d8676b645c5c6d578988cf5fcebbcfe0235; original global index 7522.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 61885c7801e9b6c5392f6de628baa5106fb5f791ca6a7e076b224aceae91c42a; original global index 7609.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6487bc73807f390dc248b17f40ded08e230542824c295b571432f180f58e7893; original global index 7834.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6633dc2eae4ee3ad3dd2505adeb8241621238b1094b978717ec9fdb115339158; original global index 7949.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 664f8f14e4ca0935ecda4bafd496c5db760dce765032348e3e6e21adc6d235f3; original global index 7957.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 697bdf7aa6f8d36431bcd2553a4f8b4cb36d795a17b62b948ee70f05cff9a142; original global index 8206.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6ade187232a4e09d09432243bd3934d5ee2a9c605e7996bbf1faef37cdd20f82; original global index 8321.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 6aebdae63370b0be3f5c70da60524f70062b11fbaca45f8c78b2ac45cb6239c5; original global index 8328.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 6da3f0ed96e9b7f5fdf9241a1ce3e945c025ddbd1c27c7aa142df54b7682c52d; original global index 8522.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6e3893ea910649e684f32189c17804ca4dc41a2f499b0df82809a3ec6027596c; original global index 8556.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00082 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6efeb1f174eb3cb9fe77050afa8c45c2e3214f9d830af646ca19a944a26f5701; original global index 8609.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 6fb7cdd5d699ecab49e512c6c2327b41fcb91c25f401b37fda6a8fad5cdb4983; original global index 8667.
def localCycle00084 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 21 1]

-- Original cycle 727d4d63db562168098cd924aeb0a52746aaf344b69694b4026157ae5d9937cd; original global index 8870.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72cc0177e8ff079c8ea2f974c5399b1276a577a6ba9f66f54fe6a052989e6946; original global index 8892.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 73136d601c5d4abaf9f458444c497f9e2e3d084c25ee8ad7319431dce541707d; original global index 8913.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7333271bfb7d45f8b823d883830bf9c1ca3d5a18e4c1534a1e51a2cdbf584d71; original global index 8920.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 742537dd0a2b4bbe3ed1950fc059be673881ccc844cf1b51bd6ec02e512c6ec6; original global index 9010.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 746fc4b81b3af471348b172212ce80b2076f33c9de8575499a87290432822cb0; original global index 9027.
def localCycle00090 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .triangle 33 1, .gapUpper 5 2, .triangle 10 1]

-- Original cycle 752ffcc13b84cbd4f56fbf5dd4370b0edb1e0c45b60ffaefbc2a544bfb4c1269; original global index 9081.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7536d3d71df16bc843111da1f305a143ac83519db4636fdc70b8b580198e3f72; original global index 9082.
def localCycle00092 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle 759f216b7e8a6f0aeb631babbdb4419fb717e1d5f9c952f2b8e72f3e775eb2f2; original global index 9117.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 11 0, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 76155befbd9140047c0bf8370f15045e56123a03b2dff59e685edb450608b084; original global index 9143.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 76cba1081143bc84f8d2b6c10f9a2cebc5eabbd8298013a21a837ef2f764e0d5; original global index 9193.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7a230980f15f1b9117429b3f8741dd1872202a8c89e9d39d6dd0c5a66d018e0e; original global index 9445.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 7a39fd0fd1769d4d0f66c0c6d1ed23a3362ef789af90b764bc4755f046d858cc; original global index 9453.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 7acec9894961ccc8dee829623406f4c62d94655a0d0823428fdca99e4fa5667e; original global index 9507.
def localCycle00098 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Original cycle 7b63484ab3d2c2131c1a36df169264756d82e7d0390b092c8cc526a72ea639c2; original global index 9554.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7bf8350514def358861685bdde9473253872f30993716c617c83756ff8e0cb58; original global index 9587.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7c93359758ae22f87bb498935e9d612f2845cc98dfde1e0c90f5057ede083260; original global index 9640.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 7cbee0f28001fc77d776e594ccd8c5f1958b9fa72dddc4e912a9d873606a2f52; original global index 9660.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7cefaca7b6ea88cb2f4e4c90d54bafccbe405fe4f566aaa6158a14535192a198; original global index 9674.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7cf406f6ff441e3075d96664c9abe72b276e1021ad514254581a058e097335b3; original global index 9675.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 84461a5f6ffdefc34313f300757cc5586698c975e26464456bb2a6409681013d; original global index 10272.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 851cce644915ea36170f5222caae7a128b0d1f9f03abc1898221b3f3bc9c2337; original global index 10329.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 86c5b5cf5c91373ea3f2e458edadb07e2687bd86a163b8389e9e2f38e5b03347; original global index 10452.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 87183690bc103c7babe43ee2747114dbc7ea0f173e60c13980adfe3831c863c7; original global index 10482.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -3, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 87cb43095da5e8681365aadccaeeeb005e8ba7b5df49ea326d052e482e97327d; original global index 10527.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 89b059826cf1bef92ad9bd8114a149c630d0ed88aa7e6da2e1ef81c0bcc91c89; original global index 10667.
def localCycle00110 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle 8b6cdc580d9f2e0760583179f59581a02e48be74a9570b1795e8800e98f51290; original global index 10804.
def localCycle00111 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 21 2, .triangle 24 1]

-- Original cycle 8fa381035d650f5ff07c04c8a0bfcbd09eb33c72a4123bea3b34db514159183e; original global index 11117.
def localCycle00112 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Original cycle 90341f33f898165abd2b12d8894b8febfd1ca8562d8304cdf1178e8e51e074e4; original global index 11163.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 91ec084aabf1dbfd8e89f78290f06dd078017d8fd8a80254895a80114e55e9b3; original global index 11307.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 950ad450a51cdbda6a2d49f103b93a779e370c451a71e4b6c63487387fab93ec; original global index 11574.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 95dcfb441d68d61f0944eaf3d9d4051e78016dfe02e6b05f691612092ccd06af; original global index 11649.
def localCycle00116 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 97c3a3ab110bead9878dea8dded3b0f827054e1e9b3dad5d471ec3ba66af0a7b; original global index 11788.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 98814f71338dcda44b585d98a1e0cc95942dd75a202815946ddb9be68e616c46; original global index 11844.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 991705c143093d4c5aeded583dfa4ba45463b2e116e134be2432412c58c63e3f; original global index 11888.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 99ad00fa49a582e33b8946123128e208fb684eba338eb0137c1606bafc1941fa; original global index 11931.
def localCycle00120 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 9a65a14fbff266985b4937ecd126e8db9cb16e60b2cd76e25fafb169870eafaa; original global index 11999.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9b3060ded5a08b2c9c6dfb2556883b60ec94c4e1f0f8a422c9bb970ecb3aaa72; original global index 12068.
def localCycle00122 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -1, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00123 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9d8d5899554c207c9891782c5f45356f61d58c483c5992b7526244acfac42d6f; original global index 12252.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 9dbb5180725e0d218750825b3c537f7ea8746bd4b930a385abfbd499c959ea0c; original global index 12273.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9e143836cae4d94368dd3a9796942d9e029fe3a418b2ebc5eff801f71f5491a1; original global index 12302.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9ee4779df8f12248d2a588ddaed2d59409637e59c66e10a0012478250dc9ff21; original global index 12370.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 9f41fcd1f5bdd4fd2e18a5778ccc08b7e1576f3e5e1f9d761f181017c9ee923e; original global index 12398.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle a6e4583eeb1fe374b786923a77fbf14e372e10bc6f29a6b96da409e3d45330b2; original global index 12963.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle a6ebda927b83fa13e4f06b0286345fb5c4b1345037569d45cd60941f25a6fdb5; original global index 12966.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a8de46fee15b16db1a30b54bba1887a1d38958f4e9f68cba96b474ae78332c91; original global index 13146.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ac8ccb771366e86e802775b0160647151b75b7d904ebd5b8c3be209ad3b1d267; original global index 13447.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ad5dec974d8d48cef06ed4ed5921497fa22d1f2beff281714d9407fefcf9cb2d; original global index 13521.
def localCycle00133 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 0]

-- Original cycle ada8fe2630001b1a8ebde95cf63f2a80e665ca30e887875569ca0d3851d4b8d5; original global index 13554.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle af24a17ab563910b5ea1dbddecf8a04df1671a0547016e0efacf819ba29e540b; original global index 13679.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .gapLower 3 0, .thetaLower 3]

-- Original cycle b13a78212c8c72c76bf8d315c304b5a9025971c16373356cd62ced44ea289bee; original global index 13843.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b253b10ed02998eb7118acbcf2f9a359cdce904fab17f2d82f4bf10f66e1502b; original global index 13937.
def localCycle00137 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b2f7b09f358aa971f151b066922fe634150502bee7101f82f3c1f3dd7ede2c8f; original global index 13987.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle b325fe0ec9bdd2282d768dfcc8744afaf15c70e3b23a87cd1ca0b4f2a0c8e1f7; original global index 14000.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .gapLower 3 0]

-- Original cycle b4d9ac179e5c66e769dda42b7b6ec26dd394421f0e270f89ddd0dd857dfe5174; original global index 14124.
def localCycle00140 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle b508a9eccc7609c138278174742b9729aac17fa5d2d856ed37d3661e29619645; original global index 14138.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle b669f99f18700681adc13b3465108b06bc81180ea8d40e4b3abccb8440ce3fa0; original global index 14256.
def localCycle00142 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle b7b22c76ee2651ea442e29e99ab611163c1b0c00ed9a676249027524d2a5926b; original global index 14333.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle b7f6deb820e0f0a74c016dee75b85f5d2f90fd1a193d96b7513c7b47c02ee84d; original global index 14354.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle ba1960dbdd5678f8a3fbfd6e047c6dbafe4f2e1cf4e66be37874c31ffeaefd90; original global index 14533.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle bd0ae0e82940fa4d934217f788f74332419389b6864c82eee5dba6fc32410ac4; original global index 14748.
def localCycle00147 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 0, 3, 0, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00148 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c0ad29e2adb936cab8527c6181a8a5676eb1c0a871b73d8331533f17c3a8b9f4; original global index 15046.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle c19321dbb69666de97c4d31e4162c91599c6f61ad1f047e5cfb007f69a70737b; original global index 15119.
def localCycle00150 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle c1d94df55d3cfe9cce29708e3ae19bc445d2e26d6ca85142b12742171a046bfc; original global index 15137.
def localCycle00151 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 33 1, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00152 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c368486fe7313a41377a3b281eb2303e11691ddf05fbe77ae7da058eeead3445; original global index 15248.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c4d9514d20955353e6653005d4ed6aad8a63c3f4da3708d55a6f728c246fa96a; original global index 15354.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle c4edb1bff2772a9023136aa4187e63f9cdab97439040d9b802f5abdfa041c246; original global index 15366.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c68b9f08cbd0a0224365eb38e7e306b6715ebc8e6cfc842f9eb096bd60adaf4d; original global index 15484.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle c6fc203cbf2e0c7b70b80a781075c3e18574ea760d3ec5e2eeb2546627691c1d; original global index 15527.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c7ef32c25271efe5940388525ea0f7eb8cc250207bb79a94ce8745f5b4900d0b; original global index 15611.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c905d8990c233d901335e7d27ea420c35b3f9dfaa7a93498e048635dfbdc442a; original global index 15701.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle cc8fb151c52c1a22397414b569b5dac2a53fc2ae47edef8b5229191d1c04aab1; original global index 15988.
def localCycle00160 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 0, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle cca62047b0b382fc8b58f974d55108cf6ea628197c5a6d9bc0dcd5726ed10e63; original global index 15995.
def localCycle00161 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle cf29a623ae84105f8f423a806278fa1d666e3062ee7b652343acfcda22f331f2; original global index 16167.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle d0ca21698e472e03e325860664f78aedf3aabd90173f7e159569f47abfc2cd4e; original global index 16296.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d1f9a7ea6dc4672df44fb747e65cad456bf94d8105abcbc02e3ecc02d396dd65; original global index 16387.
def localCycle00164 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle d2fea683287af5b80ae7ad5f515c2b17f921e4122a076a8b4a2c8bce5344f38a; original global index 16457.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d6f79000f382e4946d211cb5ff77208a92e3f5dfea6fe4e837e4cbad9a9865fb; original global index 16782.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .corridorLower 4 6]

-- Original cycle d840d61db4573497ad807cae18a2666ccbca07f2856aa75b9f270eeff28b122a; original global index 16880.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle d8a417dd2532b26b67f7696766aed495dd8dc031f3368d94f26c88ee410dd1af; original global index 16909.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d8b959e3ebf966242ba9b6810ac09bfbc830eb9e2f3f0ff4e665f8442ce97d81; original global index 16917.
def localCycle00169 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 2, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle db7de85895bc517635beadfd5d8d3dfc8bc9113d46f1fd2c621f834e6d0af111; original global index 17156.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle dcfb3ecfd345dce44ef04f531e3aade94b1971d50373d32946dbbd0a600f9e6a; original global index 17274.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle def0a8c7bb9de467777c7e868236ce77a88a5d8cc10b67f6438db49b5ea0d298; original global index 17429.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle df6ac8ec5766cc0bfcc6126de798c2200b122fe2936d619526196cc0cfbea020; original global index 17458.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle e0ae0b2f76484472628d88e20f897bc3713c5a0cfc67c77cc8d120c5574b7ff8; original global index 17568.
def localCycle00174 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle e48cec96c95d92fb5390abe26d27c28888efb47e97b156f3229b4ce2ab3eb79f; original global index 17866.
def localCycle00175 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle e4c4e989a59706eb8aaf65b3d3e5b26ff30200e7539056ea5cf6cb61a2b0f0f9; original global index 17881.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 33 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle e54925086159362b0d5ff0d1b0ac1ccbf3bbb2560637a6437c50a540e0156752; original global index 17925.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e60a1ce3e8c53291fd606786c8940f4608f6a3857638aa83341f7565481306d2; original global index 18004.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e721c9ffcce710f6d52a9582cbb008d27e09c050fc7839a972ad3091095a8a1c; original global index 18078.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e7661f7b0133690e166924e6992ec5364544b3d2daf9f1099a62aa7f939c863d; original global index 18101.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00181 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ededdc75a5401922c264b78363880f059da7984c485330f34a62993df70fa939; original global index 18576.
def localCycle00182 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 10 0, .triangle 11 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee639fe3505fb79702cb229643469bc40b62e73c8ce217192615c30f1d745f72; original global index 18609.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ee64d74f3567e826849823f40e37d59db28578c35529517629ff5e10ce4d5fc0; original global index 18610.
def localCycle00184 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .gapLower 6 3, .triangle 23 1]

-- Original cycle f0a986f10769885be27b9fb8f544f4df249c6a24e9a918ffd224e37242937e35; original global index 18771.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f15e7a77c25271ba76100e56a740f4d286141d2b292e65372707faf40f312982; original global index 18818.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 3, .gapUpper 3 3]

-- Original cycle f1b91b650ce34ee954a88f05ba53770a75be65d202f1e59579c0c36f4ae9f965; original global index 18849.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f52cce288fc312199903906b4246fcc0d5709c86711d5e1ddde8e9009303d2c3; original global index 19112.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle f751c72c3f0df9daaad8a4e8b0ca88c46dc48327806205c6c4305e4c90285e98; original global index 19292.
def localCycle00189 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .gapUpper 5 2, .triangle 10 1]

-- Original cycle f7ab840d59090c031753e6764632446a45eb0e7c0e9a2be4f00d6fbc77069ae0; original global index 19310.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle f9280908c5d67f5473628b5201e897a890c31c8ffa610c2629e6a345179f5313; original global index 19432.
def localCycle00191 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fa475957f588ba08ea0a6368b1d1853f1fd1fca52f0f2808d5e72fb0f578d9a3; original global index 19521.
def localCycle00192 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 24 1]

-- Original cycle fae49af8d47da8e871e81c009e25f9e3f349332f6ba6b367d818121134d64a7a; original global index 19579.
def localCycle00193 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle fe0d15375d56cf16cf430f2fe7e37592088d2989d18c195d766101f3ef598d15; original global index 19853.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fe37fb6f3c50e5058105329eaf1efde927fe99649238014b919cd244ceb742e4; original global index 19870.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

def library : Library := fun id => if id < 98 then (if id < 49 then (if id < 24 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))))) else (if id < 36 then (if id < 30 then (if id < 27 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))) else (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))) else (if id < 42 then (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))))) else (if id < 73 then (if id < 61 then (if id < 55 then (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))) else (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 67 then (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 70 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))))) else (if id < 85 then (if id < 79 then (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))))) else (if id < 91 then (if id < 88 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))))))) else (if id < 147 then (if id < 122 then (if id < 110 then (if id < 104 then (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 107 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))))) else (if id < 116 then (if id < 113 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))))) else (if id < 134 then (if id < 128 then (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)))) else (if id < 131 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))))) else (if id < 140 then (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))))))) else (if id < 171 then (if id < 159 then (if id < 153 then (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 165 then (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))) else (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)))))) else (if id < 183 then (if id < 177 then (if id < 174 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))))) else (if id < 189 then (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 192 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))) else (if id < 194 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 156 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6400)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6401)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 149 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6402)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 173 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6403)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 180 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6404)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 113 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6405)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6406)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 51 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6407)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6408)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 32 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6409)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 32 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6410)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 97 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6411)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 59 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6412)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 3, 1], ![2, 6, 4, 3, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 96 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6413)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 188 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6414)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 0, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 22 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6415)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 70 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6416)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6417)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 149 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6418)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 173 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6419)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 180 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6420)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 190 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6421)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 51 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6422)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 113 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6423)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6424)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6425)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 21 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6426)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 63 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6427)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 63 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6428)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 97 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6429)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 132 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6430)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 32 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6431)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 32 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6432)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 97 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6433)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 132 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6434)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 50 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6435)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 188 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6436)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 138 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6437)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 70 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6438)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6439)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 14 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6440)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 45 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6441)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 101 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6442)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 101 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6443)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 178 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6444)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 124 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6445)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 101 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6446)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 101 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6447)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 178 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6448)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 76 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6449)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 76 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6450)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 128 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6451)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 76 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6452)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 76 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6453)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 12 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6454)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 62 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6455)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 62 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6456)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 34 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6457)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 105 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6458)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 78 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6459)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6460)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6461)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 17 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6462)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 179 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6463)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 143 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6464)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low6 (![72, 66, 181, 91, 82, 164, 41, 53, 194, 36, 23, 92, 169, 6, 142, 142, 92, 142, 144, 159, 92, 2, 167, 92, 36, 150, 155, 92]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6465)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low6 (![58, 140, 195, 91, 82, 164, 41, 160, 46, 36, 147, 92, 163, 168, 75, 126, 92, 122, 79, 162, 92, 88, 64, 92, 36, 150, 155, 92]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6466)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 157 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6467)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 157 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6468)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 157 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6469)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 87 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6470)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 87 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6471)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 87 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6472)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 1, 4]], proof := .low6 (![100, 35, 120, 186, 16, 152, 161, 119, 74, 172, 74, 74, 74, 189, 90, 151, 151, 151, 154, 15, 8, 8, 94, 177, 27, 176, 30, 118]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6473)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 106 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6474)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 3 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6475)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 42 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6476)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .low6 (![171, 158, 9, 186, 139, 152, 161, 99, 13, 107, 73, 73, 73, 39, 182, 81, 7, 7, 60, 67, 4, 93, 94, 177, 27, 136, 86, 118]) }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6477)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 106 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6478)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 3 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6479)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 80 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6480)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 114 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6481)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 1 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6482)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6483)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 187 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6484)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 125 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6485)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 185 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6486)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 20 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6487)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 56 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6488)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 10 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6489)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 10 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6490)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 103 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6491)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 56 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6492)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 87 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6493)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 87 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6494)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 109 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6495)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 109 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6496)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 121 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6497)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 102 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6498)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 109 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6499)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 109 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6500)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 121 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6501)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 83 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6502)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 47 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6503)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 18 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6504)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 183 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6505)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 183 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6506)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 69 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6507)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 129 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6508)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 24 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6509)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![2, 0, 5, 3, 4, 1]], proof := .tail 68 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6510)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 0, 3, 4, 1]], proof := .tail 104 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6511)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 104 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6512)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 127 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6513)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 127 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6514)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 165 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6515)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 193 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6516)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 165 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6517)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 38 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6518)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 166 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6519)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 77 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6520)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![65, 5, 0, 84, 135, 37, 85, 48, 44, 145, 116, 133, 175, 61, 117, 43, 55, 29, 137, 52, 130, 44, 89, 191, 40, 153, 33, 148]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6521)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 11 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6522)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6523)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 131 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6524)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 71 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6525)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![108, 5, 57, 84, 25, 174, 141, 48, 19, 145, 98, 110, 170, 123, 117, 98, 110, 146, 49, 98, 110, 19, 184, 192, 134, 111, 98, 110]) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6526)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 26 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6527)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6400 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6400 ≤ id.val) (hhigh : id.val < 6528) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6400)) = true := by
  let j : Fin 128 := ⟨id.val - 6400, by omega⟩
  have hsum : 6400 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6400 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard050
