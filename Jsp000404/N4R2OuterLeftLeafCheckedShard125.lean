import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard125
open N4R2OuterLeftReplay

-- Cycle fingerprint 00522db10d2f309398d5491d4a77ebaad97512ca18005fffa68a1c638e974c2b.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -3, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 22 2, .triangle 3 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 028b3023575146d4eff8a1982e14e435efcfaeeca22275b4eba8366ecaa8aff6.
def localCycle00001 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 029a00da8aae491c98df23ef11c4bc2c53b07afe55e57f8ff9b3bb1981672eb7.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 0412fdca986565b831055c22f45a4944654fcdc67ebbb86c624069c566b4207e.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 0420f9104cb2a92e6ed3865acfd49f3efd751dd23eddd1f1a575f838fa481008.
def localCycle00004 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 050948aecdb1e2cb05c9348e0695935fe03ba2f7e038cb5c243c3a4e9b9ce0de.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 0a38deafcd2c7fee6ac539bcf42d745192ed326478b3fce01555c8a87bd5fd13.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 0aa8ffee5ed8ef2eb58a2664ae6c2a57b6c25fad15f62ba1c4e82ac24750bb0b.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint 0b48dedd92bfdc273c6d91f9cce2485ad6ec2eeed5788a99eeaa89d9c0719e40.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 0c95280905d22aba479544799928b79683707d038bc6ecd908933ce1f1517fce.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 1059ed0a4871401677badc9bf00c800d50fdc143608b5e8fd8118855d4d9083e.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint 10cb8caa3cf588be095d0624ce3ca6262ebe802f77d0dcf6ddf60892b14a296a.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![-1, 0, 0, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 2, .gapLower 1 4, .triangle 2 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 11a0c256608af31cf04a4aa3b65ae939d46c3155bebf7091adbc2814b9b34343.
def localCycle00012 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 11d16f406aa212171437554da4db1bcfaaf554c7fe4bf41143765966931dfbbd.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 136747a71b78f76cafaeea8f18c52d9c34290af898534a9c6dc80800f4b54a02.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 15f2a6b4c914162526d2ad604df46679a4b816f100bf064bd50e4e21082c7fcb.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 17e0ea3ab1ddd52fae235831b19a40fb28ccc377913d346835e31cebd3393710.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 18a37aac05d72587a79f92c6a211116baee3f7ed3c5dcf33c8a1c711f8ba3677.
def localCycle00017 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 1c32b96b4eb3d53d5ce6b52b14703389fad967ad0dc8617430fcdba1fb59759e.
def localCycle00018 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1cd0b36258702ceea93f8638d2525d72731599c918a014c3dee17edfdab1ff49.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6]
    constant := ![-1, -1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, true] }
  origin := ![.triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 1d1c3e8287bef30362185e17ad2b37b5881b695db152777c3ac53ac5f6cf44ed.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 1f8126606c7130bd590150bd188165dac182369a1fe22546b119e5b4dedc55e6.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 3, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 1fa51dd091f7d3fa1584456156fc017faf34459bdaa081a4a0ed62a0f47d86a7.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 2096cc885a79a2d816559503cdd1450d87adf5a7e60fc8d725368a7a19f8e70b.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 237c5e9b8fc14ca90aac4a1fe08e4c1b03b72f21c152baafdd60a673747d9d60.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 258d70daed5533dbd6b12a059f86af345e7878f98cae71cc9381a9d5e995819e.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 27c7d76f68377c8fd9852516593461b55e5e5f7cf2f5a2de58206c523dca1332.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 284947b1bb2b2f10c985a7cee004452de03ec4fa17dcfc5a5eae3609f00ec70d.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 28e3e6d8192d0a62973884999267d4051bb99a5d48c0f04ccc6dc3cd2d771041.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 28fe1768d02894fcf59ee21b7af6bcdaf26fed95670f0e28433334e39a36ac46.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -1, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 292cd649136633fb53e468df8c97534e4506ef92d7b9f6ff638697962f1601ea.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 293b074c238c4a282236c66145c9d15595ae777da747a15f85b9ce1dfe54a04d.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 297297a617c3222c20a588d28147da38da024daa553539bbb1177404c27d7acd.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .gapLower 1 4, .triangle 2 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 2b95baa462e35c54754eac5979d7f9a918f39247847c65979940b0728f36180c.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2bf24dfd1fbae0a108bf9406fa165c48d529e6d646380deaab95fd8909b4cb71.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 2c3b5a7f62537d05750abf3c9a201fc14bd94605ad753452fb6d42de9c1aa870.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 4 4, .triangle 2 0, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 2c87b1ffe460a915f180eb886ebd2e2cdfda266db8baf330cdb3532668095bfc.
def localCycle00036 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2cb54539a6b2e8a3c77eb0875d478a14023615844069ce19faabbc674278c87c.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint 2e08eaa35bd32fe2a533ceb4c4824c420b4b07692e5cacbd020d2e852ca52153.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 2e1154610b7a8b470e1f103e9336c158c8780416252fa3b9076eddd438a12441.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 323cac298668c4e6d5ce51dfe8e4546a00e25fef3572311f56e3cf29791cd9e5.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 32cd71190024702913af75aa294800651566cc54181666ebdbf44c64ab521d84.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 32d07c10e51ac84cdda5de1a63bc64a9be1c2147df4e1f6c0f50b45c7eeecb11.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 4 4, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 33c3df96f5fff99743f2ac34cb945d3b997a306c5c508a01e0b0645a4fcf6956.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 34214bb8aa2056af340f1b37c29ec741cdf3e79493caf57d26d83149ff63f425.
def localCycle00044 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 35c556a5b89d3a8ae20058a3bba746e64da62f7c1460a369b68a54f8639c3937.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 37425ba7b4a2409fa4b7603d595b62777aaaf165c1792bd0f0433c4760a9e63d.
def localCycle00046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 3788087aee42ec8605dfe1dd20f8c46cfd6776055bb5f9d6f630e1e70db93499.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3978b4c8a4686f6fb0094d8591c9c72d1f3aeae1235d38238cd96748919a6366.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3b018d5b0f2bcf1bd029038ea145032fe7aa6bab7036ff228701fc91fa03cfff.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 3f3b6269a0cb9340e0a402438beb631388765ad1af0904388b2f026209b53a25.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 40ee78c599490bc0b21cf92478b782b0e3050649535eca0a6850074c583473f2.
def localCycle00051 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 4221e8cf79d8a1cfc20e2a39ea7837b05a6a2608ee5a19a3cfa421bec1610d68.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 446a476536296c78c4755cdefbcd6634f4dfd915dc2ed2cc308192d68e228d5e.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 4882602241752d453b35ecde9fd529fa9456fc1df27eed6b84d1247c3e827ca5.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5]
    constant := ![0, -3, -1, 0, 0, 4, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .gapLower 3 0, .gapLower 3 6, .triangle 32 0, .triangle 34 1, .gapLower 5 3]

-- Cycle fingerprint 4885f556048b1e1e54592407342180859cfe5bdb754b17e4856965d0cbad3ea9.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4bf9fdc2b0e2ebb0239c17c03d576f9dd333aeb50261ee6ec7a89a3a9f1af892.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .gapLower 1 4, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 4c021d87396de9c01a45ab1374dc7ec1a46e5f70175522d313914d9e98e1a36e.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4f4e873cb554b5b86c844f435c846847554c5015cf102267bf18db3d429425b4.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 4f85833a6219e71a4d414124653aa0d1315dcb241b7cd90a1fa8531e9bebeeaa.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 506c2a6d212ef18cab2a9445c61befa901df360b4f746466ed394a6f2a7e164d.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 3, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 525699589346395067ffb1999f50d812d22600d9e95228c48a65453e1b51601e.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 52f95b6cb277848a0184e6e68b20e9f27b4bb85985e0931748ebb02b754e6b89.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 542ed6b41f3a6d5ea1dbbcb10c3c2741590e02779f27e4f6c0630ffa82864256.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 5616dc56a526c32c1b7cc1fb6c775a6ce9d4c4dc32500fe62132cf2593e4e5fb.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 59288445e596f1de18ece0d5cf90a6d6d9db5b827472c8253bdd28be62ac38ad.
def localCycle00065 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5945e5575c6c38dca407c3c5ede2a62db960c98c958b6d0f96a8973b428768d2.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 594ca081145fd80ae7cf66deb667a1b4d716fa1b0a76228184c121f6e0d928fb.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1]

-- Cycle fingerprint 5b18beec81ba057628d699d0fd06e4bb7807267595dcf7a021a47a4821073852.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5b6fa368630f9f38476b4d41336cdaeee1aba9e76a4c3553f4f472bc7ae78ab3.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0]

-- Cycle fingerprint 5c51b907ce7edf30aa8452f61b6644666d70c4d23240766d8e5b2d68b2310e51.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5d85c58ffb5c53ed2f6d829878700494ebbf27d9dee705c7cd5a607fbcc336da.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 601cf6df7bf2ef87909fee3dba2fc45fe25328099d079c89dd685c9bfcc627f3.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 2, .gapLower 1 4, .triangle 2 0, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint 61a4a25f06345bef884994f0530c43fd87fe0557ab56ad5ed484a7f7c88adc16.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 6563ea477a9bbe61a51bfdb18573c75aa0866976729ef8d63d27a1e2a452678f.
def localCycle00074 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -2, -2, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 65d9d7dfa23c1901f2a475ac3228370706b5a6b8bc0928ae016602f45d4493fc.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 689ef9ebf7977f55c9d91b4461885721c2deab232cd558c43013b6f6a947746d.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![-1, 0, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 6a8155ba4d4153bd3ddcf05b53064cafb19d785e1c21e209ea3938880528c7ac.
def localCycle00077 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 6b880b4ccbe86cdab03fd91dd185daa8e715f9e7a05e992700c2f2f69334d4fd.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 3]

-- Cycle fingerprint 6bfbb046e99c23f1af67a88173d736f39410a246c889b4d0aa4471dde888aee3.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 6d65f2bf6348f44f0c1f636e7afe6ff31a74c655019c85a4b4f30064ec3d8815.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6f817ef88aa9c154b8573ff90af859e26b7cbda38efc822e4180dd8b048dfbb5.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 76f0e3a0f6488eb1c7e7ca15f75c87bbf136106d21abe94a32e5c520f854c52d.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, 0, 0, -1, -3, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .gapLower 5 3, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 78f8c53bb27ed4d0cdcff2d4e41ac55a569a837347109130ee7c90676b0599ae.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 2, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7a0a1205ae0f1adae6f66bfd71ea895d1f20b2f8b21c75dc762f599f0d4b9728.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint 7cc39aea6a4550eece08d95acb0cb17cec2f6037013d484868e8fee12e2895eb.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 3 4, .distance 2 4, .distance 4 6]
    constant := ![0, -3, -1, -1, 0, 0, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0, .gapLower 3 6, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint 8272a2e89f54448aa3b3bdcccda687b2718601ac2025219b0fa7487add3d1dbb.
def localCycle00086 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 831c58f6b54f50b563c157bbfcd39554e3c40c010471bb8b36102579e11c10b2.
def localCycle00087 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 85498bac3de7718780c66393816b1b38c236194cb9897f312fc1813f7c21c41e.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint 885428be3efaa6567a40cddcb0364c2c6b8214d671a64e6ae2cd4541668db381.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 88b8706a971645d9cc30ce6ae3f746fc992251e469fd045f56b42435fbae472b.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 899cc2e16549b25e6a409d32bf406d671c6cc07d69727224c059a5dff3b7bce2.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Cycle fingerprint 8a5824cf13fa18e9cc67c791214e49dac4c690487ddef8ad1a1f18f5f03db0bb.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 8e7c166dece3fc2c6e52c4ac72ac95177f8d607bdcaae24aa7501bc2c1f58dda.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 9282fd13c31c8efd8d1a549cfdd1a59488d94c4da1cfa945f9b8df11b294a14f.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 935ebe763e61a18bdc6bd3e5c64bc94544015eb7f724e1b4ded9650e063a633c.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 94f5879b91957dc9e451e32b5dddcad3400d47dec741a9b82177d9c51c19ddd5.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint 966a61badd5e2c6f3be86b94d54c55b6f3687d65028ae174a6453409afa29e69.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 981f0b58bc30d1e6c21c23646a8406a2e6c95c15cec10de6cce4cc063595e86b.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 9a11e8392aed5d358c0a111500eceb9d91f7eb9433c0729874b1425783bf60ad.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint a25f8b465e93100807566bc60683a35df4bc0d02d979f9c10a508487f5a14e56.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint a2b2f559c8f454827d50280f0f76a3fcf2df36f76990192fe68773088cd96a4f.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 3 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint a3a14ae9260d246d539f9b75caa296bfc05bb4c18e5c3dd8699f2f606f3150e4.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint a40de5f02d7818e266882a0f3a5a3a875123a44aeac76ae4d5d474d46ea20247.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 4 4, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a7b62d31852597d12a31abfd11cd4b233b4d48ff4c177cee971a478c925c093f.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint ab305390996e66fb00816b2bb5fe64dff828cb3b890a7e3ac4a9ad76281c2122.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 6]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint acbcdcc3c3752927f3c91f31b152007f7897b697fe9537ed672971339c1aac7d.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint b021cae9eb770ffd167c8090969b3d60f878a7f65108d8997844011a5017419c.
def localCycle00107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b3a3c97ecfca7e8839b54c98312e9b9bfbf3356829c9fd0ec1c5c9766c7390e1.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 24 1, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint b4cd21be72f90c0042e49aaf4787240eb6a173959b124d1da8c3746c692adbc3.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .gapUpper 4 1, .triangle 2 1]

-- Cycle fingerprint b555691c9e41fe66c7f6c3ed48b1e11e811132195eb98009dd484327bf102647.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 26 0, .triangle 31 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint b5c16deba29ed206350160a77fc1cf7b0833c5f26a9f56ac2943d58fc5206065.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 2, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b5e9af6fc23a2ba190c1c4617514d9c699419e1df5add3788a61a7a58faa7ce8.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b683009d029b04138ed23eaa9a654f0c4f8365b3d07eb5d5aa9fa6fc5be6c2bb.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 2, .gapUpper 4 2, .gapUpper 4 3, .triangle 2 0]

-- Cycle fingerprint b765d9ca7b7053bd93f8395b600dde58bb05010bd8525f7939fdfacc33b05abd.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 30 1, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b8546572f019cdf262cafb857ca681ae0b1a50662164a69d769e91436a5e6a11.
def localCycle00115 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6]
    constant := ![0, 0, -1, -1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint b918890a657356e13f753ac6b32c31bc720f9c489f7a56c76020c7a4e3bc837c.
def localCycle00116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint bba27a22d912e5b00dc80a969957d6406246db1394e6c4609e445e9138b48259.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint bc14a4f19ad858fe3b638e06779dcf4cde34a4b09c72075a214f3ba5a4048e7d.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![-1, -2, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint bcca7729307326253022c1d7e7d78b60af6cdfd048f07fd4ce5c4754578ff4c6.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint c0577427475a8e8f9f790bdd730152ff54b291c16bdeb7d32fa951e6de39778f.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 2, .gapUpper 4 2, .gapUpper 4 3, .triangle 2 0]

-- Cycle fingerprint c198114e6d616b8de2d32bbb53a087ef1b127304c69645509068ccde8134e7c2.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint c2950b4dd2ca8e68572d38078d9988dff63fc5b40409300f6852fce830aabe3f.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint c56be835c75c5d92a2853189c450ef251c412437a01852a8020bf9bce0036c8e.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint c67b72179b08eb6bec5b0b390d919ac196c6d5530c0453838f39c2d13e1b001f.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint c8493ca2639fd68c5c0b993d13fc85931f7fd36a1257caf16fe71442d721f8d9.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c97368e73e26d65cfeafe257581a87610abc46099546f76b63cc2d6f59776afe.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c9946805f7e0b365b21f0374237316b338781fb909aa80c9661951c6dc069437.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint c9ecd577303435f9469320c2673c1fe1cb2de4792cc1d622b83e7a571c1281f6.
def localCycle00128 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ca1c3028b5934c33bd07217b5aaea37e9ffcedf4cbe4544a20402139d1cd98fe.
def localCycle00129 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint cb1b6cde9ae98672485689a0dbf3da464f9727860a26ef4118234910310b7b4a.
def localCycle00130 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cc6bd091b0da17b9d12499a5b34531ab7e8ad082562aed3bb3f20cdf90614bb6.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint cedf33c5a1dd8cfb99521577af88f6549053629e4377b66d38f41f1ae231cb32.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .triangle 19 1]

-- Cycle fingerprint cf6a4c2eac1b1b019f415c208c4d1bb6e2c1cb73e017cf47d8ffe0a97ecf011a.
def localCycle00133 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint d106b29adbbb391425d4d68144fa6e7179d7db5151cdb16ae0d2f9cb48f843d7.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint d17150954d62d40688aad3b445ef61b0c990038f26eeeddcdc1b22b6d1a4fc14.
def localCycle00135 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint d64810972f515f4626bc9d3f4af23eb2feaabfcadafc2031466d6adaa8ce1725.
def localCycle00136 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, 0, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 29 0, .triangle 34 1, .triangle 22 2, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint d6fb63c6f1ca2b7aaf00568682c492057254aac2c4f191a44b67cd9843a27924.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint d78af44c277e29b2a41b11160c2a81740c9d01ea6463987001f080a4e9cda77c.
def localCycle00138 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d958164970ba1afa325194d52350e60530553e11c153ff838daf24f27f3640ae.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .gapLower 1 2]

-- Cycle fingerprint d9d0abbaf33edce92f63d8f6b38d372880fd98d280fc832c24571f91c8c42eea.
def localCycle00140 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -2, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint da76436100fd7fb07c1202a0256d2e3fe74ac1ca90fa5ae4f720f5127649dfdd.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dcfbdd449d7d59a8f5d39a99649f49aa1bfaf379eb039477589fa201898de499.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint ddf4ba65eea08fcee9d8203f49a647cad88fc9fa8982b43b7fb593dc6b2c0f18.
def localCycle00144 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .gapUpper 4 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e01565e03613365bb62b7948c0eb030fe83071ef675e5c4e5b0eff6bf061bdb4.
def localCycle00145 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 2 2, .gapUpper 4 2, .gapLower 5 2]

-- Cycle fingerprint e19ed65019f07eee3455c4d87f9181296128b0e44bb97343e0f18f5b2980779d.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint e2b4ae4651861de99406fa34339f7dfc59b218d04ab977d004bb9ce117c5c5a9.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint e31bbd950970f81f818c49e7cc31345d6ec02ad4c609d9c7e591fc8eb7ecd972.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .gapLower 1 4, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint e34998523bd8bf87540b29702dbd7902cf73d9f10ddd9bea43077b4a6d2a7067.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 20 2, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint e377761a98ce21f46ad068dffbadda369711bada52166008b7fb5c3ab0607ec2.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint e638aa7bbf1776c87f9097c8196014daf8f5b30bc6e403d37b970567708fe1a0.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint e73a64b4d3f649d65a2649747d86a93eb9181359e7e63d00110883236feecb97.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint ea09b7c3fc1ee65dabfa3a19fce7ae773dadb0c43e3e312bf2aaa80a181c9106.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint ea4aac4848b0acd6cbbc3516ca6127f49ac58cb8b050b6378d7f7bdbf2f7092a.
def localCycle00154 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint eeab0c65708c26289d8d0a8a6d8a38ca0485302b4041109544e68d6fd9f074d9.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint eeb311410e4a117395ce96c80ac6ac6bce1fdb1a910a396767e20624b8b18740.
def localCycle00156 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f069f1d318156af5ac16acbb2ff1660ee33efd459cfeea787246022e23c00ba5.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint f68108910e70fcd532d2174643cb4f25aaf3b72c4ad72bbf951299b8e77d5009.
def localCycle00158 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f688aec60e588e0e6ab51617e283c8313ea752b1e2a38adb24dd7bce80646987.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint f862b1d210faed7f302b620cf09910a7b3bb5ae245c5d01eeb3b200f3fc9280a.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint f9065781c5aeccef888938732fbb84374793fe27f1acea331f32c29938ec21ba.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Cycle fingerprint f9a7ad921db5aabff16620d46a729ed5ac831408a25ba13ddfa8c97d83602460.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint fa6ce74db817a6dd46d54bc81de15da4d3408965ad76303e78491d01ca098800.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint fb26762c6ed62fcd3f8e86d3afc1c2db93289cbe11790ab72d8aca20467cb561.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint fb87d373797513c6da118025fb6d3cbfd44bc004caa522d356d3846f3614ebd0.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint fc10da62052f525aa26252daeac4bc3d2915199d7e4291f293d5cb8adb529058.
def localCycle00166 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fc11b93dbbd3720c63caf929f412fac9b75ef4529926f6c1137b6ff9061bab1f.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fca0d801dc7cbe06b6d6bed31d7e1d41f61654cf4479f7ba78fa6a024caf2afc.
def localCycle00169 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .gapUpper 4 2, .triangle 2 1]

def library : Library := fun id => if id < 85 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 74 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))))) else (if id < 79 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 82 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))))) else (if id < 127 then (if id < 106 then (if id < 95 then (if id < 90 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 100 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)))) else (if id < 103 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))))) else (if id < 116 then (if id < 111 then (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))))) else (if id < 121 then (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))) else (if id < 124 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))))))) else (if id < 148 then (if id < 137 then (if id < 132 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))))) else (if id < 142 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 145 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))))) else (if id < 159 then (if id < 153 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 164 then (if id < 161 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 2, 6, 5, 0, 4], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 80 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16000)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 6, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 45 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16001)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 143 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16002)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 2, 5, 0, 4], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 23 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16003)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 1, 3, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16004)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 1, 3, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 155 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16005)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 5, 2, 0, 4, 6], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 1, 3, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 30 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16006)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 13 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16007)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![3, 5, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 9 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16008)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 162 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16009)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 34 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16010)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 121 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16011)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 50 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16012)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 121 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16013)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 77 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16014)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 5, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 142 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16015)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 101 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16016)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 5, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 2, 1, 5, 3, 0]], proof := .tail 142 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16017)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 1, 3, 0]], proof := .tail 15 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16018)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 81 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16019)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 160 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16020)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 126 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16021)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 160 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16022)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![3, 6, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 79 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16023)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 143 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16024)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 3, 5, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 168 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16025)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 131 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16026)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 88 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16027)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 2 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16028)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 128 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16029)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![5, 3, 2, 0, 6, 4], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 119 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16030)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![5, 3, 2, 6, 0, 4], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 38 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16031)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 103 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16032)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 38 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16033)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 35 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16034)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 58 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16035)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 8 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16036)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 42 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16037)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 42 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16038)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 97 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16039)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 3 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16040)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![3, 5, 6, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 68 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16041)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 137 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16042)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 120 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16043)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 5 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16044)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 152 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16045)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 157 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16046)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 164 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16047)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 4, 6], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 117 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16048)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 3, 2, 1, 4, 6], ![5, 3, 2, 0, 6, 4], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 109 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16049)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 3, 2, 1, 6, 4], ![5, 3, 2, 0, 6, 4], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 40 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16050)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 3, 2, 6, 1, 4], ![5, 3, 2, 6, 0, 4], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 16 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16051)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 104 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16052)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 3, 6, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 24 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16053)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 57 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16054)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 43 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16055)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 124 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16056)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 169 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16057)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 3, 2, 6, 0, 4], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 27 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16058)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 3, 6, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 90 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16059)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 124 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16060)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![5, 6, 3, 2, 0, 4], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 169 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16061)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 3 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16062)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 3 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16063)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![6, 5, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 73 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16064)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 113 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16065)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 3, 2, 1, 4], ![6, 5, 3, 2, 0, 4], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 127 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16066)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16067)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 5, 6], ![1, 0, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 4 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16068)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 1 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16069)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 112 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16070)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16071)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .low (![78, 144, 100, 82, 54, 61, 134, 71, 75, 83, 118, 140, 46, 53, 163, 11, 105, 107, 91, 11, 141, 102, 76, 52, 129, 147, 108, 39]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16072)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 21 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16073)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 5, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 63 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16074)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 51 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16075)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 114 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16076)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 63 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16077)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 26 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16078)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 161 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16079)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 166 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16080)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 20 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16081)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 5, 4, 6], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 146 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16082)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .low (![59, 144, 29, 0, 145, 85, 134, 71, 75, 136, 44, 10, 46, 115, 14, 32, 151, 116, 74, 32, 99, 102, 56, 153, 129, 25, 108, 39]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16083)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 94 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16084)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 130 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16085)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 122 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16086)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 28 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16087)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 161 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16088)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 3, 2]], proof := .tail 123 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16089)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 3, 2]], proof := .tail 96 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16090)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 4, 6], ![1, 0, 5, 2, 3, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16091)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 3, 4, 6], ![1, 0, 5, 2, 6, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16092)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 138 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16093)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 135 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16094)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 3, 4], ![1, 0, 5, 6, 2, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 22 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16095)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 106 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16096)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![0, 1, 6, 4, 3, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 98 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16097)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16098)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 69 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16099)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 1 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16100)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 51 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16101)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 70 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16102)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16103)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 48 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16104)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 87 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16105)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 158 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16106)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 125 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16107)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![1, 0, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16108)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .low (![86, 144, 100, 149, 148, 84, 134, 71, 75, 111, 17, 65, 46, 53, 156, 6, 67, 116, 165, 72, 139, 102, 31, 66, 129, 132, 108, 39]) }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16109)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 47 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16110)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 154 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16111)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 89 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16112)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 36 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16113)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 89 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16114)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 4, 3, 2]], proof := .tail 62 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16115)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 125 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16116)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 2, 6], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 33 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16117)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16118)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 167 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16119)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![0, 1, 4, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 55 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16120)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 133 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16121)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 150 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16122)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 159 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16123)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 19 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16124)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 64 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16125)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![0, 1, 4, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 92 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16126)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 5, 6, 3, 2], ![0, 1, 4, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 93 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16127)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16000 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16000 ≤ id.val) (hhigh : id.val < 16128) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16000)) = true := by
  let j : Fin 128 := ⟨id.val - 16000, by omega⟩
  have hsum : 16000 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16000 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard125
