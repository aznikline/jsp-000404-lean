import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard096
open N4R2OuterLeftReplay

-- Cycle fingerprint 0294361cb185bf2e44db237eb745fef310c92f74de7f29de074319f450f922e8.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 044161d26118f741dbcc04a85c4d3060b0dedefd418b476d59ee30a6dad0c70b.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 1 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 07a9e874b000017761a1453c45c4cebece92bc542ca92c9c33c9c1b2afe90701.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0a34578460ab457624852163b70ac272769e49d9c3dcb60d5ac4f385bab40e9f.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 0 0]

-- Cycle fingerprint 0b3c7134cfab40ee3f81b863e96079b7f2151fc5afc801ae43ce18e931741d8c.
def localCycle00004 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 0cdcc95d4a6fb44c077b0e7e29dd71e828c5e8b1bf60c4de7793752ae7bcd412.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0db7b8960b3db83ca136491bd7158498e36f77cd0ea921f2927cb3e78d7ed980.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 0e7a77ca17c6bb0196b3f76d0154043f713047e33a6d97b98be4da07a09a25e3.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 0]

-- Cycle fingerprint 11ee190e48c96d1a3189bf24188d0e6a2e223027b92e9bc7c677d729fe013919.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 1baae5681c194b112cfbe7431ce655d438035a403a29aab52a8a6155365c43f4.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 2]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .gapLower 2 0]

-- Cycle fingerprint 1f431f22911ea90528d0096affad574c5cab6dad7ac7088a1e4cede68a2a4b4d.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 25a607abad24aa47950119c6dc501bcc6e755469e249d0983b33d29493413c49.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2b33589706685eab906b1f3cc697ea162103892da9b65c459a169ef6c8ce73a2.
def localCycle00012 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 2e724dcdcee8aa07df8c971ff6ff87d1d87eb6075c83614da0abb091745f6dce.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 30123377b2d8b7fa3bd769b79593f2aaa40488e92bdf9011e981524a0bcd63a2.
def localCycle00014 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 31c7d8cb3ea36c5ec7b1dd86a4141f44436551e225aef0901e61612f863571e3.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 33cc1d5c25e4b6d990c4562e83162b77846704a278e42a4c136dfbe24388734d.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 2, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3905d7a903d6c0b256607fdd712a81984658f21731f5b3f08a1b4f9a5a9e854b.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 3f9b2f9774c309e0b3c08e5acce9623c3ca7eb1745ef26d41e65733829fd10b4.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 417665884ac149127a38e8808f76e144e4d2fe99a805260a5b422d8dbc9b8e59.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2]
    constant := ![0, 4, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 6, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .triangle 0 0]

-- Cycle fingerprint 455112c5780b9a421fbdf7d78643e678ddea1388bc95f36dce3e5f7a4ee074e4.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .gapLower 2 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4655d2f59e2c979efefaacaa325ad0221fcd23d1ad10e717cc0ae6c03240c09c.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 46bd9304cea6f5337af6561a92d0912f936d3806b6744def4e8e40c0af757145.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, -1, 0, 0, 3, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 4, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 4746a6155d23a80d351029965fbc896fc147791ddb6a874f5e756ef6bcea307a.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4d98ab669aa8fe284a7ef607eb72a3ad4ad08f23e4769ab81ac7c5ea5b0455ed.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4e4850603ecde2c717cc96d017cdba9eb758896d2a701b58e18909473fa92bfe.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 50391b31f056452a728307c39e475e6aa3a6df8b73ab5d1b1b5dd16c94a89d29.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 505ea33278cf02745ca1ff4abaedcd5920c7fe15f82887947876c25da9499bad.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 4 2, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 523485d6623c7247f4a740f6c4a7702d5c72b4497f47916b2ad23f3eb936aa19.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 0, -1, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .corridorUpper 3 5, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint 528b03051d9c823d5b6df7b1d094c4c690e1f3ff35cb4e3c5b485ed492dae6ed.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 546ea0772ec93d24dd64f21487a066b9046ce02e700e5fb785d49bda0989e5cc.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 56216fd89dbf5caf0c00c15e828ca766b4e233fb77ecab916a40b0f37e74c443.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 570b1ba49270efb37b55dae20ad422e9b28eb5a91110eab23f0ae208b519db3d.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 58df6a89b130c78fd48d0925640663d26d81d01258cb28bd0b151103b567f43c.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 5dd7a26dc29ab6261bee1ce823e264c113822106534b72393b6812ca217bf1c2.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5e0e0ca716fa595f8f6606e4bdf2726ec1f083c17e181ad5e88baa2164794953.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5f7af76a216673f45998e01dbbcce5e0a8e7b0bf46d511a989a02af9eb9f5fb6.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 621aa2f9a18cde70b064a2db35574e89b22cf75f40b14f54d9c1d2f3c8b2fdc2.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 6307a83212e5a243d6c7c1166f93c8eae45d9218519ab327fb00dc7ad61fd6c9.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 698313b21102abb9b46619179b695f1337ac7eb024b88d958452c247c326ad27.
def localCycle00039 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 6e2ec19084a0f74a7df1750bd77737c6bd9dbd6074f33f5dc7fd6ead9def24a9.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 73afb96e9eafadabc7f7c09990411c4e48868760c7deb8327e175b1af82f85f4.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4]
    constant := ![-1, -1, 0, -1, -1, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0]

-- Cycle fingerprint 7afbe4de89a9127ef84d03d9991d449fa893cd97eb6c18c76bd94e0f176f20d2.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 2, .corridorLower 2 6]

-- Cycle fingerprint 7ef3035bfab67867d9ef18eda2d0506b6447934c3c06ef3feb44ea8194381991.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8073186f225c4dbb7705c7369d1542b087067bfa62ad45e002ebe6decfc6034d.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .gapLower 2 2, .gapLower 4 2, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8358603aee874079ce3ce2713c5e9e9078ccbf13b4a57cff7779ee0099b0b5f4.
def localCycle00045 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 838086fe6e5acedf011e9bb3d7fdc861c650118d90a39f7f7e3a21fd9b7424f9.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .triangle 15 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 86a9f0fea16eb1b5dcf619156254b8177d35ae4976b773f25a12c822849b42b8.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 873418b21bce4326147be207774b9e5a7602ba9218421b6d307f455a115f434a.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, 0, 2, -2, 0, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 2 0, .gapLower 0 1, .gapUpper 2 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 88748a8ad99bd663de83a41ede47fece47b1c0174d9845daacad7a6ef2c2ea75.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 89ddd2648b082aee0811d4e0180242fc5d30f80628d513d16c936bfc67d55153.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8cecdac1fb6eed50e0f32e4733f4158af337246953618c4e1ce1ace84a0cc50e.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 2, .gapLower 2 0]

-- Cycle fingerprint 909f50f663e580097b6c5409f6c414d498540dd6840c384e1c382b2e257949f8.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 946730efc116c768b562d145add21b11d47b36327896de6d8ce4671c99499cfb.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5]

-- Cycle fingerprint 99efc3b64e677df0368d3e936a1662978ea3c80a12075e00a6a6fe0cbf6c1f50.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9b9b2128eba4a069cfcd2cb862b156aaaa8d1d1e715c7103c133558d30bff87b.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9bfe1b0fde0c61e805d5a15b664bcb8da5333f0a66d5f75f84d92da4d64505f8.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9ee22ab624cc26f8b06d32c689c04a893abcba75dcd87534e738c7b57a3dc5f4.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a85195eccb8be1e5ea21b4f6db09084dcabe7afb539c110ee305e84fab505e6b.
def localCycle00059 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint aa0eece2c060ce7eb15bd7653b36e731c0d518b766b3d863b6e0a18e54b26c66.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac4de46dea8d4cb9dd684eb4d388073d36c4810dc254c74560485a384945db94.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint adb01122c771d323810236e8f34212552d36c38641bf6b1fafbf218ec31c6027.
def localCycle00062 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint af496cba716b876de8bdf9bad40cfa7001412fdf88575508bfa326896a562ba2.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .gapLower 2 0]

-- Cycle fingerprint af5a068cdf04bf5868caf59946f210fd79ffcdf6c151a39671de9afc54ad542b.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b0d57a7c02fb6b1761deabd3ae6b97e4636eb309f53b18b85dc91a4f8fa21e27.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint b219cbfb79a89c1ef85e426e7dc08133bf2042209b7437a57fe5044f35ccbb95.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b32c0f13de0663a7ca4e67734cfc68d1b8898df3c1cf344c234edbd65ed25b24.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint b3cb3bdb387fea6fd3553fff2d1d34d49214eb40a69506d1e502885999c961ef.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 0 0]

-- Cycle fingerprint b66023b64177f34dc711e9ec386175286c87b4fe099aec577de82abcae5758a3.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint bae7770bef65a687cbda03b164b08037c1559f4361c930acec3ef9e4f9a775e4.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .corridorLower 2 5]

-- Cycle fingerprint bfb277d7d4391650ac0a6af292651d16b31bf2bfa0f14db84612535de8929d53.
def localCycle00071 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c2154f0eada953d0679153d83231fe2df02fc19898e8982caefb588b1aeb1a49.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -1, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 30 0, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2]

-- Cycle fingerprint c3f487f2d5ca031e1e45d083bcf11681b2787248a21492fe598ad4b2ccc013bf.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint c4ff84887bb6383c1b39db914a3b9c1af9c796580db2d7fc6d0c136b9e5b7d4a.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c55fa5e2043d41fae3020d6f8c4a45dcde6a2cd10bd83aaec014b6145b197bd8.
def localCycle00075 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c65e684d98c210e0b585e0aa6f2b218fe05e690df0fb72576258e2ccebeb6b50.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c74371dc20f18eb693a48591b56f699d66fde873f65b78557677c6c4f3e85b6a.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c82ef19af8b879b22fd445a3c8d2f4940b36a69d918e7a4e076cf9e88ea44372.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint ce7d9872ee323d9a06467a70fa24f01da146be9707fb345859e696fc00bcef54.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint d247df028c6ee1c3feb1b15d3fc338fe25c1df3bcc0694dda4ef67c87cc0081d.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint d2b8f177d4a5f50f1ac4524a7cc9c18bd812e7071291f22761cd62fe60a4e411.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint d2fefdff582cf6445e01d363b30064aac36ba33f2571344a3832287bfa5558ff.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint deb393382ee3b0ca7b8043743f5cb5372a96066e8985bba225acccf0c8a24f4d.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint e53797ba7943d349444233a71cde9c1604b5ebec9cce8fd43f2d0c1b7de144d3.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e659b04b19bacd93895f602e0ba720dab7f225e593cb0779a395877cacef1ba0.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ec0830bd664b0c4907e5c819ff0ac7db0b914a528cb0238bd6e9ad04caad65ba.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ecb49bf2949866a690da7b2edb5103a02d9391c08a6d483ff2fd15ef163c15a5.
def localCycle00087 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f1dd1d29cb73dd91044091114fab8107b9abd57bd8cac48efbc2a8726d69fd24.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f5cf5e2a8181709d8a8cab3a4700df6f6bfaebab3f7357d003ad3bc2ebf2255d.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .gapLower 1 4, .triangle 19 1, .triangle 1 0, .triangle 0 0]

-- Cycle fingerprint fd0eda4131efe9dea6e6400ab7b3c8bacacca5f562686184cac502b879d24ed1.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fdb2d3e1e0830f923d618082e18d5c649c93ca96bd9936392f04f1fa83d4ea0c.
def localCycle00091 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

def library : Library := fun id => if id < 46 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 34 then (if id < 28 then (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))) else (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))) else (if id < 40 then (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 43 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))))) else (if id < 69 then (if id < 57 then (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none))))) else (if id < 63 then (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))) else (if id < 80 then (if id < 74 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 77 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 86 then (if id < 83 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))) else (if id < 89 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 2, 6, 5, 1, 0], ![3, 2, 6, 4, 1, 0], ![3, 2, 5, 4, 1, 0]], proof := .tail 37 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12288)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 2, 6, 5, 1, 0], ![3, 6, 2, 4, 1, 0], ![3, 5, 2, 4, 1, 0]], proof := .tail 63 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12289)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 1, 0], ![3, 2, 6, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 31 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12290)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 6, 2, 5, 1, 0], ![3, 6, 2, 4, 1, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12291)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 1, 0], ![3, 6, 2, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12292)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 1, 0], ![6, 3, 2, 5, 1, 0], ![6, 3, 2, 4, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 42 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12293)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 2, 6], ![5, 4, 3, 0, 1, 6], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12294)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 6, 2], ![5, 4, 3, 0, 6, 1], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12295)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 4, 3, 1, 6, 2], ![5, 4, 3, 0, 6, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12296)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 4, 3, 6, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 32 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12297)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 20 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12298)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 44 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12299)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 35 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12300)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 0, 6], ![2, 1, 3, 4, 0, 5]], proof := .tail 85 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12301)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 44 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12302)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 85 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12303)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 27 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12304)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 0, 6], ![3, 2, 4, 1, 0, 5]], proof := .tail 27 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12305)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 11 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12306)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 1, 6, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 6, 0], ![2, 1, 3, 4, 5, 0]], proof := .tail 8 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12307)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 44 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12308)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 1, 6, 0], ![3, 4, 2, 1, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 8 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12309)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 27 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12310)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 1, 6, 0], ![3, 2, 4, 1, 5, 0]], proof := .tail 27 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12311)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 86 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12312)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 7 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12313)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 2, 6, 1, 0], ![3, 4, 2, 6, 1, 0], ![3, 2, 4, 5, 1, 0]], proof := .tail 7 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12314)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 6, 2, 1, 0], ![3, 4, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 70 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12315)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 5, 6, 2, 1, 0], ![3, 4, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 88 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12316)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 1, 0], ![3, 6, 5, 2, 1, 0], ![3, 6, 4, 2, 1, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 5 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12317)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![4, 6, 5, 2, 1, 0], ![3, 6, 5, 2, 1, 0], ![6, 3, 4, 2, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 34 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12318)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![6, 4, 5, 2, 1, 0], ![6, 3, 5, 2, 1, 0], ![6, 3, 4, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 17 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12319)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 2, 6], ![5, 4, 3, 0, 1, 6], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12320)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 6, 2], ![5, 4, 3, 0, 6, 1], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12321)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 4, 3, 1, 6, 2], ![5, 4, 3, 0, 6, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12322)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 4, 3, 6, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12323)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 1, 6, 0], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 53 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12324)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 36 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12325)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![3, 2, 1, 0, 4, 5]], proof := .tail 6 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12326)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 1, 6, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 1, 3, 4, 0, 5]], proof := .tail 67 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12327)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 36 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12328)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![3, 2, 1, 4, 0, 5]], proof := .tail 13 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12329)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 69 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12330)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![3, 2, 4, 1, 0, 5]], proof := .tail 69 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12331)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 43 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12332)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 1, 0], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 47 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12333)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 1, 6, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 1, 3, 4, 5, 0]], proof := .tail 87 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12334)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 36 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12335)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![3, 2, 1, 4, 5, 0]], proof := .tail 65 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12336)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 69 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12337)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![3, 2, 4, 1, 5, 0]], proof := .tail 69 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12338)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 43 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12339)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 1, 0], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 65 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12340)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 70 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12341)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 2, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![3, 2, 4, 5, 1, 0]], proof := .tail 70 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12342)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 6, 2, 1, 0], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 70 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12343)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 1, 0], ![5, 6, 3, 2, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 70 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12344)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![5, 4, 6, 2, 1, 0], ![5, 3, 6, 2, 1, 0], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 21 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12345)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![5, 6, 4, 2, 1, 0], ![5, 6, 3, 2, 1, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 21 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12346)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 1, 0], ![5, 6, 3, 2, 1, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 79 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12347)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 1, 0], ![6, 5, 3, 2, 1, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 18 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12348)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 4, 5, 6], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12349)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 4, 5, 6], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 46 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12350)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 25 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12351)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 3 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12352)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 30 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12353)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 3 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12354)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 68 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12355)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 39 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12356)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 16 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12357)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 24 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12358)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 2, 3]], proof := .tail 50 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12359)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 3, 2]], proof := .tail 14 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12360)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 2, 3]], proof := .tail 59 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12361)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 3, 2]], proof := .tail 61 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12362)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 1, 2]], proof := .tail 62 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12363)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 16 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12364)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 24 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12365)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 50 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12366)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 14 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12367)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 2, 3]], proof := .tail 60 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12368)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 61 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12369)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 55 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12370)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 1, 2, 3]], proof := .tail 60 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12371)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 1, 3, 2]], proof := .tail 61 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12372)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 3, 1, 2]], proof := .tail 15 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12373)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 83 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12374)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 64 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12375)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 6, 0, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 1 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12376)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 3, 4, 5], ![6, 1, 0, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12377)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 5, 4, 6], ![0, 1, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12378)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 5, 6, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 78 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12379)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 23 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12380)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 5, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 89 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12381)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 72 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12382)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 38 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12383)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 22 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12384)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 58 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12385)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 51 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12386)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 3, 2]], proof := .tail 41 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12387)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 45 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12388)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 3, 2]], proof := .tail 74 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12389)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 1, 2]], proof := .tail 73 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12390)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 58 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12391)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 51 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12392)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 4, 6, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 41 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12393)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 4 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12394)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 3, 2]], proof := .tail 29 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12395)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 3, 1, 2]], proof := .tail 40 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12396)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 1, 2, 3]], proof := .tail 48 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12397)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 3, 6, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 1, 3, 2]], proof := .tail 29 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12398)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 3, 1, 2]], proof := .tail 0 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12399)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 48 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12400)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 0, 6, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 76 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12401)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 6, 0, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 2 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12402)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 3, 4, 5], ![6, 1, 0, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 28 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12403)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 5, 4, 6], ![0, 1, 2, 5, 4, 6], ![0, 1, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12404)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 5, 4, 6], ![0, 1, 2, 5, 6, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 12 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12405)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 5, 4, 6], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 71 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12406)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 5, 6, 4], ![0, 1, 2, 5, 6, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 91 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12407)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 5, 6, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 84 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12408)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 9 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12409)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 19 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12410)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 3, 2]], proof := .tail 26 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12411)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 5, 6], ![1, 0, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 49 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12412)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 82 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12413)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 4, 6, 5], ![1, 0, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 3, 2]], proof := .tail 66 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12414)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 4, 5], ![1, 0, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 75 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12415)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (12288 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 12288 ≤ id.val) (hhigh : id.val < 12416) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 12288)) = true := by
  let j : Fin 128 := ⟨id.val - 12288, by omega⟩
  have hsum : 12288 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (12288 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard096
