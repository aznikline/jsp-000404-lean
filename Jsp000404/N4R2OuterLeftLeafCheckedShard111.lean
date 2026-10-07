import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard111
open N4R2OuterLeftReplay

-- Cycle fingerprint 00e3b8d069eecad79f587ef4619b45b5e9fd908e2c37db04777ce7e7b1439abf.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Cycle fingerprint 03a62d21a85e58953a3a6731dac8263ff26143580defe69da2841cd2b6237c96.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 04dc517f59e096fddc6ee4c3c24819f8b6dc0abe4623458b6e56da0654b24cb6.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0a48df223235b845f390441938e2581dfc30eb3db59ae6fce83f8cdf623297cc.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 0c5dc1e1942c7d8e7135685cce572659da196ac1b1cf3ebe256a20258534473f.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 0dbb487edde4a9be6ed445068f3fd11de35ea60e4482667facdecddcf6fda1d9.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 0fdafe7c5950c0c562082a154d44432a7c01351c18e908297910bce1e9408a91.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 0fdc730aaefcb43afb83a535c95b0ef5af9af34b3c4badff8765682974b4b14c.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5]

-- Cycle fingerprint 15b8420c5d23b89e8ece3b6d61133a9e5ba20662bd97b7d31f8e6427f9ae805d.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 17c2d20e31a70cd92eb929355ddffef045f9a2f48564530ac8771d9ae6648d76.
def localCycle00009 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-1, -1, -1, 0, 0, 0, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 1c0583273709e8d90473ee3f18dab223593f6d42e5ccc27593be7921fc08e108.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 17 0, .triangle 30 0, .triangle 34 2, .gapUpper 4 3, .triangle 16 1]

-- Cycle fingerprint 240ced006a93b5edf1407a36028dedcfe4c6e2dc3ee91b1c4e9deecc52e77c66.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 25c08db3adfc854449b0a3de645417f12b4463a11dbd53cea2c4012c9161dae5.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 27325300a1a6b6da15fbbc8a59dc028b991a583569df379716f21915bc429e87.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 294e1aa82c09d52533ec873c06a2c83652370f5d1473057eb2648d7d88afce8f.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 2b4d8ac667e2c34a6da75f0c4357fbab6db8f91bdb57a84ea6c21f06f2d1b8c9.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2c588bd75aa45b73515e05ad9762e7f830f103452dbb71fa0bd475e6ee3ef101.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2f888fc1ccda2403a793edaa91b8d014dd39233ac98e5e288272bb5410a654db.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 310e84cdfd7e7bbfa672b9883b59116745bcbb547656e5b353d52c1b21a9b684.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 36f14e68669bef25bf784e758cc07c47824e97b89320a131927fd78963b886ca.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 3d7dcb4cdf64e0f1758c1989c8164b392e1b24767f31ca23262670b578d39ac3.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint 42432514d4ea96dc8b63d6635c5e128abad7438db063e379b6bf53ab21023068.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 4b576cea04cfd055071ecb4b560b5137137bf6f81edc7184bdbd794d698a7ec9.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 4c0df4dc744fcf814564d7989babb243df94770411eec767bb07a74c7ee9d69e.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 6 0]

-- Cycle fingerprint 4f87badd9272b29bc68ca4e9422bd5ed09fdba4af6932d2f944885fcd1f02839.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 519eed48591d6b2a712acc5aed9c655b3fdaa02362cfb9bf9af0694a7654cafd.
def localCycle00025 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 52a4a4621fb1aeed284958bb25b17b3a17ae3497fa229ca1db545f7fbe2aea02.
def localCycle00026 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5729219ee274fcb013eacf60d0774ba637d4fbfce22d0417ae36ca10af24947c.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Cycle fingerprint 5a7e5d8351c5969847726c129f74d16c0423783d7314f09b635141a1754b9a48.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 5dc58a65de39699604ce2d9a2190c358087a2743b0c0d416b070da7c4d046f77.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 654f6cd92619298c20d7819b1abf9f19a72f0d4d17d5d7f684e0106a14178ff3.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6aa1908c79cf78e9949198cd1f43434ff381982282b2024cf1b20cc5373aa111.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .gapLower 2 0]

-- Cycle fingerprint 70a23ca49044cab3ddd300fac0d7c60e73d48b9570b2dd020528d6afb52909d2.
def localCycle00032 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 70ec8fd5a8b826e5464190518ea8a7118d70f83f2dd8c55a2e517d3d169721e3.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 7fbab4096b74f30b8cb347ad9622011d14b8ca5e6a21dcdc25e4d98cc909842b.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 833d672b30b96e7cdb9a66bfa310ab5e8b37f3b957a28665cff9b890d2dbdd70.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 83919d909dc995ec99e1001855fe4693ea5e58ff8eee5626b9fac61da862c994.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 83eb4c82b7a257b9512f30b1fd6920064354110309370897930dc1233321713d.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 8609e4ce7f4c260ddd0130c688c9bfd780b82545deace74d8cb9f3ab334a8546.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8745fb6d6c45b08229fe2b1a66a09ddc65885ff8f139a074ce28b648b87e0462.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8783a661ab873010c25de2a4c8ee242d694b9192e4c629373b821afe3860917e.
def localCycle00040 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8b01b7942ac70527c8971b35067d9092b8f4f149c6aff70b8d50cc88c8a8a548.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8b4b7fafd276bb1e78265f3df72cf676304413b2a6576449d2a7baff81921fb7.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8cd0fb99c4fc56001eeb8a7bd695081f7b7dea70fca8e7d20e168322d049cc0d.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 8f59bde9be21ce9f668f7c9c806a0720464e8d47a854bbeff0ba50f5f0f6cc83.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 917b1249d2246e3a2a344681aae5075164079df70510ef54cd3b5a2d3c924deb.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint 944c4dc633a028f5e70119a36d25b934ee087f83403ebea9b9f1f4da5c429464.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 952c3a2c449e0e6a4edadb40a90bf0692a43e3d82612dbbd7179297df99b26aa.
def localCycle00047 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 98bf33acff38fa203c75bf1868da494819f2b0dae0ccc37d1dc44317ed30bcdd.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9d2eca660af4dafc9b3f972883a07d605c1b28906c0a77802462b8550beb177c.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a38d904bf25edd7314bbb1de365f970ea8089916bc4737cab86f3b993932729e.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint a69357ece5c1ff5c6704732c7164ad58e4e8a406722f6c533db53d9f9f3b2448.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint aac3708e3773f40bbc951b9a1d6d8b4040a110b10f2445a76b21bc5e7a5e91d7.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ac1f5b25cc549e5491d0a34ddd6a8b22a452bb85a494a406a1243b5cc605dd3a.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint adedc6d8fc48517d191d5d3fcb54829099a860ccc1fbd5d71388fe749718b65c.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ae065f87dcae5b5e58a81146b5a88c5e03bc0b008fd75ea5cc8381168db2d673.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint af3d98115ca18debd0a71f0a980056f6e8940f5670abbfd26cbdf16771ed21a5.
def localCycle00056 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint b20f3d306fd880a0d797019b7f90186813da2b17f100f60326b81601e9115ce0.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint b3dcb6385f4b34f50c33d8aa660e32961ff1f848f4b02defaafff5c66e652694.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b4513aec12a8868efbdfaf92a3f3833250406c7cc7dfd3618158ee723132f141.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, true] }
  origin := ![.triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Cycle fingerprint b4686e0de4918e643f5114a0e6c6d08a4a046ffca0312cf8f0e1a9e29815440d.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b4d7a1d1b07b567ad756a7de0150cbd9ea507852b48b9a5e81cd6d19d8fbfbef.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint b4f44b384f5687467dca9851b8ca4a5b5459ff02ff376ede73567532088346ac.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b9ee7517185663ff76aa5d3c4ceaed15118db44c26607a3790a7dc69abaa926e.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .gapLower 2 0]

-- Cycle fingerprint ba14b9b2719fa371769fef44af7f0a242def5b4f7bd9e19127a8d964e267ab95.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint bb95c41501810ab45e87716eaf8f62da383ffc948d42581348271b572192ddd1.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint bc7f9b9d3cabf42c21e76d5e47ca4a6762138e048ef3d15138d351424a2456ef.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 2, .triangle 8 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint be0a82b69c08539aff4fcfb581d757e40f9293c340ba98ce143d2bca39c0c8d1.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint bf11351342af6a824ad6b67c6c14d9868a59181936d9ee29dc672693005d2b6c.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 2, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint c0d4ca9c89a6dc096c12d0df2cdfc21587b313c19fc21d59178b50817a604a29.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Cycle fingerprint c8708665f4af62d71c0e91fbc70569569aa9baf884699093340a234c225b52fc.
def localCycle00070 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c95172b626105eda263dcce59b7360827b4ccc24236628495fc1192aeb6be14c.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint cafeb841d64a23592fdb5dc8a558db95d4ef9b3ecbcb9bbee515936c523d0e82.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Cycle fingerprint cb371216db8f95f3f0f57332e5a47f5e7df6e152a76b5983329dc53de1ea547b.
def localCycle00073 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cf8ba0a63f1d9e59021e039383312974c3d5e5b041760f22226a10754b77f7cc.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint d08882646fe0f6219a059ccb7901e3afa32d3fcacbeece37ae6416bdd1a06a93.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint d4aa8b8639d5becbfe8d73367e290cbf0c839bbab7cb77444f6452dfbd6f4ab7.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d666b1750f7d3adf9f9a7b4be15a165fa0610d74f6da63207330813a6a18b58d.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint d6a9df6290757a85330c98f8b27f7baa7fb2ff223119970fd01848adfdc89a62.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint da7a8205fecf25c9230fe815f91bbd6d73cb33264907759a991a705e1def39fa.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint db8788f6667ba66cdd0b1b355909a56ae5331a880dc4da177d7c4f4a1d8c3c2d.
def localCycle00080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 2 2, .gapUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint ddfefbb84762de1abffd9e8e8c068cc96e24310b2307209c12043078f5cd2eb7.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint de825a1d9a9b424d0cf5c6f0bd04b29216ea5a56802029f1367bcdb667e41334.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 7 0, .triangle 30 0, .triangle 34 2, .gapUpper 4 4, .triangle 6 1]

-- Cycle fingerprint dfa4442b1b8136a45d1bcdfb60112d3da537a430a535b3727de44792a823049d.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint dffc6058eb51c8f07e3574ce6165512193750dca9e99c869dcd942c698a0f95a.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e08993ef04176771351b35970ce88d8a73d9627f833f9d0f39cb5e1876c87dc4.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint e2eb655a919b35ce7fb6642288d90e68a716499b64a2c011dab5e7d11da3874e.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint eaa60e3d03e34d19075443b9e671690edfe605059eed66eaa6ce731370f1664e.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ee4eb0f74ea33b97696bf763f62c31c9217f0b8bf0c2ac4e5b5fde3888699353.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f034f504274979fa21cbc67e1d4e9af83c81e35ab2d6e749e79e562d7819f810.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint f6205d1e0955771a3d124f1818b38df58eaa099cd3e0125adea5dc709deb87dc.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f623fdaa573994e8b67dc756d7f4ebb9c065021f3a0ad33ed9fa50385aabdd0e.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f66ad2c9f6cfd2acf8d4fad989989997d9c41ab23b0308751aff3134efa84bfa.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint fb941b4b3cdc63cf000bd99b05d137f8127fae20f76629d382fd712bc68fb184.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint fc24cca21ae32ef12b49480218ecf1f36174914bae56c59dee292476c838e4dc.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4]
    constant := ![-1, -1, 0, -1, 0, -1, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 13 0, .triangle 23 0, .gapLower 1 2, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2]

def library : Library := fun id => if id < 47 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 35 then (if id < 29 then (if id < 26 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))) else (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))) else (if id < 41 then (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))))) else (if id < 71 then (if id < 59 then (if id < 53 then (if id < 50 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 56 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))))) else (if id < 65 then (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))))) else (if id < 83 then (if id < 77 then (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 89 then (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 23 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14208)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 8 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14209)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 2, 0, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 6 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14210)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 13 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14211)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 52 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14212)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 2, 0, 6], ![3, 1, 4, 2, 0, 5]], proof := .tail 46 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14213)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 2, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 7 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14214)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 6, 2, 0], ![3, 1, 4, 5, 2, 0]], proof := .tail 82 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14215)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 13 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14216)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 2, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 13 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14217)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 6, 2, 0], ![3, 4, 1, 5, 2, 0]], proof := .tail 19 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14218)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 1, 2, 0]], proof := .tail 4 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14219)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 52 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14220)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 51 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14221)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 19 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14222)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 4 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14223)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 40 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14224)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14225)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 0 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14226)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14227)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14228)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 71 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14229)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14230)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 41 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14231)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 85 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14232)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 85 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14233)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 73 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14234)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 2, 1, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 85 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14235)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 2, 1, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 85 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14236)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 14 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14237)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 2, 1, 0, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 14 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14238)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 2, 1, 0, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 94 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14239)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 1, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 85 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14240)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 2, 1, 0, 6], ![3, 1, 4, 2, 0, 5]], proof := .tail 79 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14241)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 1, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 79 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14242)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 2, 1, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 56 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14243)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 1, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 56 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14244)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 75 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14245)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 42 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14246)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 90 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14247)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 10 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14248)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 2, 1, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14249)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 2, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 85 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14250)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 72 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14251)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 89 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14252)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 70 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14253)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14254)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14255)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 3, 6], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 93 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14256)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 30 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14257)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![5, 2, 4, 0, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 78 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14258)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 24 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14259)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 2, 1, 0, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 24 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14260)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 2, 1, 0, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 22 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14261)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 13 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14262)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 30 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14263)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 2, 1, 0, 6], ![3, 1, 4, 2, 0, 5]], proof := .tail 46 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14264)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 13 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14265)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 3 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14266)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 2, 4, 6, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 2, 1, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 55 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14267)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 13 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14268)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 2, 6, 4, 0, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 55 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14269)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 62 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14270)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 62 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14271)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 48 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14272)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 10 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14273)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 83 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14274)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![5, 6, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 51 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14275)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 18 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14276)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 45 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14277)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 35 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14278)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 5, 2, 4, 0, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 17 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14279)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 2, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14280)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 49 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14281)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 36 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14282)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 47 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14283)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 15 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14284)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 15 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14285)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 25 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14286)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 29 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14287)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 29 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14288)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 2, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 1 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14289)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 26 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14290)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![4, 2, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 65 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14291)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 2, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 0, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 38 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14292)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 6, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 50 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14293)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 81 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14294)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 4, 0, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 88 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14295)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 33 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14296)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 80 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14297)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 4, 0, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 37 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14298)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 4, 0, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14299)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14300)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 20 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14301)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 92 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14302)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 11 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14303)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 6, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 74 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14304)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 4, 0, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 5 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14305)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 53 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14306)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 4, 0, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 53 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14307)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 2, 0, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14308)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 31 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14309)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 2, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 43 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14310)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 2, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 0, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 67 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14311)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 6, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 67 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14312)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 86 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14313)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 4, 0, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 21 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14314)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 12 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14315)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 44 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14316)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 4, 0, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14317)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 4, 0, 5, 3], ![6, 4, 0, 1, 5, 2], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14318)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 1, 2, 0, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 39 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14319)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 3, 6], ![4, 0, 5, 1, 2, 6], ![3, 1, 2, 0, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 54 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14320)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 2, 0, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 68 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14321)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 6, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 68 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14322)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 3, 6], ![1, 4, 0, 6, 5, 3], ![4, 0, 5, 1, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 32 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14323)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 4, 0, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 2, 0, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 28 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14324)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 4, 0, 5, 6, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 2, 0, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 54 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14325)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 5, 6, 3], ![1, 4, 0, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 2, 0, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 58 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14326)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 3], ![4, 0, 5, 6, 1, 2], ![3, 1, 2, 0, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 2 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14327)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 2, 1, 3, 5, 6], ![2, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 2, 0, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 9 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14328)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 2, 1, 3, 6, 5], ![2, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 87 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14329)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 2, 1, 6, 3, 5], ![2, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 66 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14330)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 2, 6, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 4, 0, 6, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 66 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14331)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 6, 2, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 4, 6, 0, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 91 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14332)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 4, 6, 0, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 2, 6, 0, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 34 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14333)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 4, 6, 0, 5, 3], ![1, 6, 4, 0, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 1, 6, 2, 0, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 16 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14334)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 2, 1, 3, 5], ![2, 6, 4, 0, 5, 3], ![1, 6, 4, 0, 5, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 1, 2, 0, 5], ![6, 0, 3, 1, 2, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 76 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14335)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (14208 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 14208 ≤ id.val) (hhigh : id.val < 14336) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 14208)) = true := by
  let j : Fin 128 := ⟨id.val - 14208, by omega⟩
  have hsum : 14208 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (14208 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard111
