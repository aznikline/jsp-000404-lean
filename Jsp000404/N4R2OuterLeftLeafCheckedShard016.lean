import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard016
open N4R2OuterLeftReplay

-- Cycle fingerprint 03bb333f8a0fc5c044fc4f2135ca677669e3c415ad08db955d58a9a8f63d6b2a.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 056be970e3c23bad3bdcfbccba693d8f68a8dc55ef8329788ec747900d7597cb.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 056d22a9891d7eb5a14624560d3d7551d37ba67b73bc048901769a754e6778bf.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 06bfc8704aab047976c73a781c9a1c63f42bdf3f26ab509f4415a201f67c1c1d.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 07b13ce310877dd96c2ded4ab924d4fcb312c2d368ab33d7eb2110be6d9210ae.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 08b4a54d2a160328e30bb09c2177dd1c228f4cce1fb5b1d338acb9ef80fa603c.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 20 2, .gapLower 1 1]

-- Cycle fingerprint 09c6500d0248f34b693bb77f284b5f347215f7be5af2cd1056f29a527ce558cd.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 0a66de26cd5a65674c6e13fb0ba367205ecbc0556c73b1cfedb5e27d8f0a6639.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 6]
    constant := ![0, 0, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 30 1, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 2]

-- Cycle fingerprint 0ad8ea0477056ae9627756e96206d920ba0c2eeb1a21c703887999edc011b496.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 0b80eab7a752322e15cd957afcf523fc830bd2c75d35afe066b527bead6ecef9.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, 0, -1, 0, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, true, false, true] }
  origin := ![.triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint 0ba237a0f34197010e5f3074558db19236a93489d98c4d1ca2142846690c303b.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 0c48d46f7631445603b3adafe5d9dc4be1b554d36ab13fd77becdc1bd25d242b.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 1774f27e2c016cca44f412e4efd8c82b62163115492363f2c516c89171e99039.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 259c4d6caea6c043a7a6d1cab4af1ff3a9be287e9d72e36ac5be80a0a3c0886a.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2a7aeb9b11eebe60ce872de95c9a4c742e8ae85753c6dabbe513d45a92262885.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2e5e0b1f472fe3e928c3d454d15014161b66d185197d753522f04da1cf7013e4.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 3329bc0c72ffd3ce4c1cfa12fef0fc0b53b547427012ef59d83bb2b3c09f6360.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3420f627a5e67af9a45acc48db20c4733c2d13d05c9c7df455e890ffa0a0497b.
def localCycle00018 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 349c8ebd262bab22065838587466fa9b7a1765a383b0ead08762cb083e3b8c0b.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 35b3fd3b16442ef5763971a8a31737052118e857f8ec7f2b06b7132a77b5f148.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 3686e7d86d001714ee6548897894ad65cb8ac3e38cdcc32e6a7015fda7b0d707.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 369e2562961e2d788abc7c4b698586e10cb0c19b7f215755371e565a79ff795c.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 369ef59ec4730a779894d9173e7074914b93dd8a9f792b5144d23d4445f5405e.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 36b8c222e9cfd222468a7bf8fbd43be4dfe523be190b093feb984aea481f730e.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 3 2, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 3938f3a2c5f8683222e8f72064032b05ebea7511bba6545a11e6166d49bcaaaa.
def localCycle00025 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 3dd905fd92e12dc7f0ac5d272e6b3292227cfdd7c7bedfe9dd91b52410b8227d.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 408c4863744f02d2faf29409f2d5665f74bf66d13f2dfcf27af6c814c6934fe1.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 42801c6007c242ad5549b500535abccfb87e92cfe7b1f8f5125d1e50c6a5814c.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 459f336ef917660098e7e314e47969bc583fe9eef008a2b8d280baa8c6613b54.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint 49ce27025db1c9da77d01caa267cdce42741b3c1c1fec7158223e99e06d95718.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 4a883d543cb7dc5deb74cfa27cecf0589e788a0704a57fc0ce74f3ca15ca9518.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 5006b6eaf0a7e208a9255e89c45068f9b66d098a8df01ef1a533e2919e7fc0e0.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6]
    constant := ![0, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 18 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 51b0518c2cf47d1483b0b05e2bf2ee76a1075d1b92cd2f5c6c21fcfc777bd3f1.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00034 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 5620c003cd5ca6873a37fba58f8b7e96a43934da6e2df479f0bcc3631a52d29f.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 579d8d0de29fb5469b27420d59ac13348e85b84a99fcc58b56394a355cc259bc.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![0, -1, 0, -1, 0, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 57cf0c6e597139c540024bd442f835a193b42925cd763bb3c72b1aac5ae21401.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5c2d655195b4f3011be548e807215faedc557e62daabedd75936d3848221bdef.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 5e3f44229e99b1107f1731b9243926b2b6ceda49f9782fcc98355ebf2d685409.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 5ecdb076cc5ac968f8dc1c64411aabecb72a681005fa136ccbb3856c1c2dc3ad.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00041 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 61dcfcb9c2f2986b66a9d111a66c0f1fe297ebf0f3de64796242be9200f9dab2.
def localCycle00042 : Cycle where
  length := 4
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 33 2, .triangle 21 0, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 626edab9950a23f7e17bd9fe1c200f535a4d8b5293a81720e618f98c209709a0.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 627b8c16c1e1209eb5fbad05f54ab40e5ac4494d876b6b68e5651bb566a743fb.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 26 2, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 62b5b7bfb520210bc4ed8093720c5e50b1f4d4e57b7f6e764377db594891c520.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 6405df57451a5c7215e5f02d526f7845f70df0946466eb64eed6693e9d6369f2.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 64bd5d57567cdef23915eaaae806dcf07c28028324e5283522a08d066467114e.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 679c1355ae465718082aac9bbb31416b5381454b6ed5f2354b045f9b7e05fe0e.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 68c7784e11062ab04fd4ba8dc786e35ddfa30d7e3cc9c88fea4ae9822b25239b.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -1, 0, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 9 1, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 6998154550cfcc65dc85ab84d61c186599921b4b5d0b44c43b65be6806116bef.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 6a663c36c5ded82e3deb491c8fffe572260607db100fa2ebc613a05c4b77d963.
def localCycle00051 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint 6ac6526d11236b4631315b26b423608959d30816f8c995f86b9c8815e4403fba.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 6b0bd716451bd1b31ddb6ae7428ef5dfea2143d5c8ca347fa385470133026c9a.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -2, -1, 2, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 6f2d3e974ed4cc0f76b619e4f50a61858a9ae94b425295a73089eadfba2bf1d4.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 72f4a7a4bdf7d3cd88b644844d2d298d06632d8352ee9ef9dfcae39a758df585.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![2, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 72fe7db0a546380298f1ccc2f4d88a374e16716b42438d185a7d99aa7579317b.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 763e3978f735da511fbd62f7246ab3e382aa6895795fab6b1acdfc0fc9254bf1.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 77eb55cc3ac9e603f336be9563063a5b9907de29397bce6549fb5eca0cda7633.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 780300fe6679f6e0df512541978fa41b9f90c49150d2153f47c6b5ca69c145fc.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 783c7f2534cf08aa2f71c6dd246efc833ca2e1953cca9e80be11234dccc17338.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 78c07f8b470e5362023059ce37ecf5a5f2b818349196d122bbd6ab7550dc2d1a.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 7971330c902863125818df70a680cf36ecfd88cba861655c142a3b71ca263930.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 7cdce45f7f3558f71214f5c2582e2cc07fa1db10693920c279333b075edc9611.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 7f3682f97edf3e7144d93c3439f577aa9d67b723cc019765ef13d3e7e29899cf.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, 2, -1, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 19 0, .triangle 21 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 8030a3d1ce5b2c0381590fa44b943ad53b6d720881a25756c7c12519cc44ddc8.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8a78476dd0803bf2c8f4521413e7080b5241826553981bc876406ca79d52e523.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 8db15a8e06d56b462dc663d1d55d7ec904ce70d5b959f576036d7d092384330a.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 8e0ff8b503d6d3ba4cc4c9757cc90af9fd308c071dd853e0f59db3d06246c159.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 981301ede43304cf737f0e6699d025c11eeb6aac3fd50d6cff30d1bd9ef5c7f0.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 9b0ce93e88462f01af442f042d0be90d893311d46050de09a3cd0c73f87815fa.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9ec7ef0ebea47afbd1a2fa3b100ba3432cc0ae0a094f238fc21d034bc043c61a.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a02cde57ee5470eba11e6bc08660a7dc78ba95d481b5b086fdd2051217d015d3.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0]

-- Cycle fingerprint a06ee81c662b95c712380805910cfb64a104a2c7a74fa419d0fc6e0912738b64.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint a2ef511ab6bd370d560ba8fafbf679f87291bc0faa30d0a0aa5c333a11c9c375.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint a5324f8d098e94eb775e740a23a8bd57c77bae90995bd64bf6bc2a1b786b89b8.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 4 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a6a32800c0d29f62dbeb82dc62653ee5ba1640d44b915d6f17307f3ce952a4dc.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint a79f099c3bdc463c6bfe3da52e7b6509a6aef104b11fe7c5827dc7616653adce.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint aadd1745fce586a87405022502acda29bf64498e659f055d1a668d71b8870399.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint ac63858f3405cc256e61c4819b2774f7602cc4684f9bf5ae68e3cce2fcc99651.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint ad84e992d12c601d8aef6f91070aa08c78028c10c27823d83680ee55d004fe11.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint adf1301a0828ca682ecfab6522233fc74df444851291243e314c3e43eec01cf0.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint b2953825aba9e3454225add11cea10e7a76ce6938b8dacb193cbeb6cf7650e5b.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint b3f526d2b4bb859e48cfee7d0de07c558f0d9017bd1d7c1d37a6f5e5b40e193a.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint b58f4001cc88bf8375c52dda07f9d659d210a0585ab2d11f32a250e00b8aa883.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, 0, -1, 0, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false, true, true] }
  origin := ![.triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint b5a32e9d650c0896526d95ad5330f8c32f5cff5166a74afcd4c4ea87a681912e.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 6]
    constant := ![0, -1, 0, -1, 0, 0, 3, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint b5d0a64c07e084aea9880e039b347d1428256ab36fc09d25e99479c274219526.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b74cc5c581e7bc20213bfdf613ca41f18e862f9d82eb3538726eabf87daade9e.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ba2b25a9c6f23f6c56983c1e63625472e7c1b923cca6903e8838ecd6921ccc8b.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, 0, -1, 0, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, true, false, true, false, true, false] }
  origin := ![.triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint bc98a7a6b1e0d4abb28bf9cdb4027e8d195663347bbd88757bec35853f4345ef.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint bd226e0c629ad0797a9bae6805b15a478cc526faab269775dbe6bc49bd1d1f09.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint bf3ce67ab7df63f40e52956ffc01d132df0905011b4852d7f7427691b3f7a04b.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c1f4f151f77d11b99e1b11d54e1a238cf2624a1e9553a9fbe4b536b507c23be4.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint c4ab2ce009e0e0e79c0a1968f2ddca7a910dc253e26a21c38c2045181cf4a05f.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint c597f235b9ec9c5b5e2d2dd25844070d6c5e7f4d35d8433dc8dd7e8029c5b175.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c8b290cdfa4273acdaea26021611f50fd2aa3c03dd0f60c1af10a6c8f06f37ba.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ce583e4c54fa3dd95fc5c2b0d673a07e11bfd7110ad79a09f9a746d0b259c284.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ce92e0e24e47132e5e3cfe38e13caa1a4eaa355c9b01b7ea4a287b8aa802db39.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0]

-- Cycle fingerprint cee643d2db74fb9f6be9d9a6a2910ce0d716edd4bda9b28ecaf47f3c8f861d0d.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf8c48edc12aa89a0ac891e0243755263720014a19b16eab9e820ea45262e44c.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint d0a7678a41325fbc0910edd8dad99d562a244e4ccafbb573851fc77af287c27c.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint d2d5ac11f74ffbb35c6c6b218fe82d9fae2c1ca765097be3e38e8429e91a1214.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d370ad67164b634c5c7ae0dc56c7beb078c8837378538d2b3355b4a8f046233e.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00106 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d709f28ac493a8f3a530c1a8239e9459b144a9e906bd84a9474176a746c1657e.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d9f00a0ba429cba9f80d2cb282f03609f18f32facf8a96a78fe0b4186dfb8caf.
def localCycle00108 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint daec27b8a60946e102a0469ce3ea6c443c8d7b19d86ac1249a8bc2079132f92c.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint db50cb21964ee201ad2577272d306bc234bda0327e03b92dd9d5a5c88c22cf7a.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint e02f7efb18aeb85bffb72199b0cfb1ec5274afc23740f62997e3702b674ce1c8.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .gapLower 3 2, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint e0bee85dd0445cc1ff33fdce4bf16f258e887363fc51fd0e9f27e03c74ec9ac4.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e244521a55a43a674d54ba366c596d09973fe6ec7d5a007ecc11abec71bfe704.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint e4602b132013a21d115da7c48e14c2b4fef2b60e51b45536a46fba11567e5fad.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint e67657616e3e494d71853a3b756483478e62198129a837a09ec60a3727713538.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint e7269ed79f039a0a62d15eeed3c0e7435862440808c6d7aa05489d2d59322a15.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint e8e4c8ddcb51d4a0f7c59633ed796615e85623f0bef99e78227f0cabb862e07b.
def localCycle00118 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint ebd84dae107012fbff8acc9dd8617e7dcae5a121896b74ced82d923e28a60298.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ecd20c5dbb8a4268308f9d4e1faf44327f5917760d797e9646825b1e65eb7e4c.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f1abdeb9f1dfdf2d27939c2ef7401eecd62224dde8e6f3d41671465259a1ab66.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint f4bc79535667a83838d48f4d804abf1a075971cb6706205f98455c3a3f0835a7.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint f4e259719d7cc9df4796b783994b32141a63d14397e29d30d7f3c63d220d467e.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f526263cfd9c4dc8f6e75977d7c2ea2126187628f0cf17a03e84e7dc768b3118.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f78f8ba23f740136e0c1a4e409ac15e91e8cd07f0d454c0a9c8345c6273db0b3.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 0, 0, -1, 0, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint f8ce0862186ccd839ee548af650b63cdf2ae6bff6b1c17a68483ff4fc10260a7.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 25 1, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint f9d98cc6efcd710320f1ac47fee71d6f2345ffea9769bb159e85f8eb551d7e2d.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint fc1584b29a9369c916b539bb24d50780dcd174b97a7f9f90ebed35a2171f65c6.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 32 1]

def library : Library := fun id => if id < 64 then (if id < 32 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))))) else (if id < 48 then (if id < 40 then (if id < 36 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 44 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 56 then (if id < 52 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))))) else (if id < 96 then (if id < 80 then (if id < 72 then (if id < 68 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 76 then (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))))) else (if id < 88 then (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 92 then (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))))) else (if id < 112 then (if id < 104 then (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))) else (if id < 120 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 3, 4, 1, 6], ![5, 0, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2048)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![5, 0, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 118 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2049)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 51 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2050)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 126 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2051)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 1, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 3, 0, 2, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 78 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2052)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 1, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 115 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2053)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 3, 0, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 123 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2054)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 123 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2055)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2056)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2057)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![5, 0, 4, 2, 1, 6], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 85 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2058)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 14 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2059)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 0, 4, 2, 6, 1], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 70 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2060)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 96 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2061)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 27 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2062)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 3, 0, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 105 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2063)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 37 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2064)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 119 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2065)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 0, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 23 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2066)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 27 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2067)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 72 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2068)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 52 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2069)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 76 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2070)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 62 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2071)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 61 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2072)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 111 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2073)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 28 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2074)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 112 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2075)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 59 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2076)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 98 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2077)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 33 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2078)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 3, 0, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 39 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2079)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 39 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2080)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 113 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2081)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 117 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2082)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 4, 6, 1], ![5, 0, 2, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 3, 0, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 105 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2083)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 0, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 37 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2084)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 119 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2085)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 0, 4, 2, 6, 1], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 95 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2086)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 117 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2087)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 72 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2088)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 52 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2089)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 121 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2090)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 24 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2091)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 0, 4, 6, 2, 1], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 102 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2092)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 89 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2093)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2094)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2095)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 19 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2096)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2097)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 8 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2098)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 13 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2099)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 12 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2100)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 120 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2101)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 38 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2102)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 108 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2103)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![5, 0, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 84 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2104)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 90 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2105)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 104 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2106)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 65 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2107)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 56 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2108)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 99 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2109)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 104 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2110)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 50 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2111)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 33 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2112)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 80 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2113)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .low (![106, 29, 75, 2, 88, 18, 34, 114, 77, 124, 97, 116, 44, 79, 82, 40, 5, 55, 25, 79, 79, 42, 36, 103, 9, 32, 87, 48]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2114)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 63 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2115)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 0 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2116)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 107 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2117)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 22 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2118)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 119 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2119)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 10 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2120)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 98 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2121)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 39 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2122)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![5, 0, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 22 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2123)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 69 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2124)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 62 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2125)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 111 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2126)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 59 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2127)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 33 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2128)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 57 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2129)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 119 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2130)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 10 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2131)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 89 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2132)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2133)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2134)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 19 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2135)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2136)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![5, 0, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 8 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2137)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![5, 0, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 13 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2138)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 0, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 92 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2139)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 74 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2140)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 26 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2141)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 69 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2142)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 89 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2143)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 89 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2144)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 17 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2145)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 110 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2146)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 31 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2147)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 43 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2148)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2149)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 94 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2150)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![6, 5, 0, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 4 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2151)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![6, 5, 0, 2, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 46 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2152)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .low (![106, 11, 41, 128, 83, 18, 34, 93, 47, 127, 30, 116, 7, 101, 16, 45, 15, 100, 122, 1, 3, 64, 20, 86, 53, 125, 91, 49]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2153)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 57 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2154)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 81 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2155)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![5, 6, 0, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 81 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2156)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![6, 5, 0, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 109 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2157)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![6, 5, 0, 2, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 35 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2158)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 6 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2159)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 6 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2160)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 66 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2161)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2162)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 71 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2163)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 60 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2164)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 68 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2165)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 6, 0, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 54 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2166)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![5, 6, 0, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 54 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2167)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![5, 6, 0, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 13 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2168)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![5, 6, 0, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 13 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2169)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![6, 5, 0, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 67 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2170)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![6, 5, 0, 2, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 58 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2171)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 73 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2172)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 73 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2173)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 111 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2174)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 71 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2175)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2048 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 2048 ≤ id.val) (hhigh : id.val < 2176) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2048)) = true := by
  let j : Fin 128 := ⟨id.val - 2048, by omega⟩
  have hsum : 2048 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2048 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard016
