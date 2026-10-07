import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard030
open N4R2OuterLeftReplay

-- Cycle fingerprint 00c4a225d149bd5b0884159ae197de1e629f37e609058772543980c25ba074bd.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0142e13d7dafe9b984131a944416cfb560fd9ee97c1470c62b0613509c92792d.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 02a6dc04b1f27a325000c6b0472a5d32187c7c7d6c7f3cf03cb30edffbcbf24c.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 0563cf5a7bc33805f3ff0162d87c5f888ebc48b513ee4450ffe2852ddddf9e9d.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 0775d6d0e4afbd589ec92122a248f4cc0d90caa8e69131c7826437cc1be6ddcb.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 09953d6a26a8491698ec1afbac2c1a5d9b7ab15fda7fc7acd0ca0320ae69aa92.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 09e71276e11134c5fd6762050b975dd5678bab03c739038e64cb099017248fd9.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 0ae1fb76613bb25be5b53d1e6191afabfb5f8854c29dd532c7ccb9d0d98d76ab.
def localCycle00008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![0, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 22 1, .gapUpper 4 4, .triangle 23 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 0bebc0f949e12787f75661184b9a3b9368a59cb99dbf126e0e99c054adddcfc3.
def localCycle00009 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00010 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0e29ddf92baa02788b70ac4a33878965b06d5931b18c3bd5099b4b390d110a5c.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 0ff3000a0139af5545b2fefb5a3d2ed3a8b4884d5475aaf3f9bf3732df45da2a.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, 0, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 106538ef24abf72ff18ec2553b9c6bc66c946c060e0799da6945c8f0a3f01bf2.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 10b524e3bf2a0a58c402e36aa0f290c2430287d2097aa72ae41efae272b52733.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 132a5855b1369d378f0f5d178ba3dce8c7525dac6b87550624cd268df54c157f.
def localCycle00015 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2]
    constant := ![0, -1, 0, 0, -1, 4, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .gapLower 3 6, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 14463d61fe4f42f1b0d9b33e8df139b216414f641498f6cadf3ba3e65bb38689.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 14b0606c9962bcbfbff33faa28d1578d30f3733d4c212145afc4fc6640ad28da.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 1726353fc4fe5b74b5d645c4302047c5437bd446f7f4a5ba03507b2a19fa296e.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 1806f7bddcdc5490f99b13a959ab8d85f9c76bb7812ad7bf865dc9105934bf5b.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 7 1, .triangle 6 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 3 2]

-- Cycle fingerprint 19c55c3b4d0cae55c3603fddf09b30be6825b926eb58f57093839e99ca1b0d74.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 1a3a309338ceecc01f922f0da68fc446e9c6b7b3266942cba2ee2e6c3c0afd97.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1ac7eca925002503c049d45a0dc7e52b1aeceaf456bf5c97c1abb5c63dd9eb83.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1c82c5c6af24cfec4068fba15916df19443777b22611b659443e057c575abfba.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 1cf40529e58ecd348f08729f700ab863b5b1f2cf1f82ba82bd38b667934f0a3b.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1d9a7054ac4f3d0e4ec6dd12b4bf454273847cfed6f90824cee19d4c04f69b7e.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint 1daec18da92906f13671bc070e806e43e965920d2546c2d98bfac671cf46cda6.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 1ddd72bc01d5b94a691b9509b741344b428e9b9bac12d5eb701915da29954703.
def localCycle00027 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 1f95d73168cb4230e808960d447c3180565a1348bf767b668323b43049d50667.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00029 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 224bbdfd4fddd5eeefe9af3f6f7811226a52c0c95d8c26cba023571110034d62.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 22fc58f6f6cf1d74f0a231a5f1829254053cc9719aae8ee9173606940367dc53.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 8 0, .triangle 29 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint 2323dbb059899cd0796971f278d10d2d460b1a769a2d1542041c0402d338bb13.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 247f64c1e480e11ce167f309d7d5b4d5d4dcea0d3a7975a7b0eeb450aa2faa79.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 24fa41057c4a9790dc911dee234b9ba5ff522b1e0ae14b3a8494309830c4f6f1.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 25d85cebf7ca55a2d4f863a664772be7df7301e0a02d2e55a2d4b10bc861e90e.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 2 4]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 6 1]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 26dfd7c651c61eb857507250e0daec6c3c037e5347ebb7a27b6db6765d9e9de9.
def localCycle00037 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 2703e0080e5b0bf3bf26b5691ce78b863be900e83198b769bbdaf73fdc0d991f.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 2746de0faf6662f3d2675bd2057c936152fcbd0082b6946bc9189762b4198ea2.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .triangle 17 2, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint 276fee3267b4477f54aa680277f99efb8e3d0a126f0e805b42e8b238240b6a46.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 27c4d3fae0b184e9394cffb92f2ad3dd666198055ba99ed84260a00c35d03391.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 29751df70ada9d9375c52576f53604c79ce2cec357eb0de5bbcebc186eda49f7.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 23 1, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint 2a6c53cafbbd6814a7a2ed2a57772d83e39742d4700e4d7271a6926f3395a522.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 2b709282b0984904143e9d52c08636ae12573568d6f2b38b6bc3ec47c2f04c63.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -3, 0, 0, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, true, true, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 2c588bd75aa45b73515e05ad9762e7f830f103452dbb71fa0bd475e6ee3ef101.
def localCycle00045 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2cc8bd78499826ff9d39c37a8c0bbf85125478903b2f5247a3046ed29d41ba28.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 2e62e9f4e08e9610c4a79c8b32152e3367727572bb7398d7b4ba72a898a6ec04.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 2f4d697d7aad1f91d2ef1001a4a1cd8c656edd361fc906c661720aecdc22d7d5.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5]
    constant := ![-1, -1, 0, -1, 3, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0, .triangle 28 2]

-- Cycle fingerprint 352b21d0cf17f580c34b12eae4027b4fc8f06d90e9d366d9e1f937718819b9f9.
def localCycle00049 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 36d9559ba100fc0be2a8cf42feb63f7a970b4189b5df917d775efc209052b3af.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 3754687bb5fdc4a9fa8532989a0e914570cd5560c26689bbef74a7b71d01c729.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 37a506117bdb8fb3974efd2392ae37b2bad590623026751ddf22d1d58fbf7ef8.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 386bc966dcfafe048927761b1147eeabe631c8f5799eea55e7928c977991dae1.
def localCycle00053 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 38a9b27d0a5976f9be0a472ea4247bcf2370e68bd0c6a3348443fec9ba8267fa.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 3b49758f63caba82d871c7a038bf27d21f1ba62a8cee098afc54313142973233.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 3b58bb7a98480f4434cc922381d708ab8e1338812a91da5f7a408d9bcc5a59f9.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 3d5fff87a4593fe40c43cc5bc9ada1bbd7f1edaa6b93c6714933b49754a7bc8d.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 3d9336099a76462830fd4f6a3a5c6008382f1a713b313e279fda99dc5da5ac6e.
def localCycle00058 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, -2, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 1, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 3e0cab9b99c7cd35f1aa0c44031756f74a0fe3cbe070b7dcc0bf0eb3e7f55e92.
def localCycle00059 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint 3e28aaf952864c95b314c4518e0020d555de7e51041b7098911ae5ecf662ed11.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 3e3a4ff8f67799ecb130cd8acc008b3ba7fdf143d3ad8dafeb8ba6fa4a571c2f.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![0, 0, 0, 0, -1, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 7 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3]

-- Cycle fingerprint 3ee3e4586b485824fdc2b2dd7be06c56e011328a618c2a240abee62215145d0c.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 3f149cc6982010c7f20eb28ee9c882f0b5ff24b3cb4c13cce4b03ab45a7aab29.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, 0, -1, -2, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 40134c081454891e18b01b23f6de9a44403ed62093852bacf124a1032c90796c.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 12 1, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 412b4f5b5ca079ea53aac1cc49b42017ae57f8f27d3fcef1ff43229bbd81dcc1.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .theta 1]
    constant := ![2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 4840263ba64d68d86304bb6480107dbbde5aa5955a7aa5b9a04fca080f5d02df.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 4850b14a9417cc84487722a25d37ee0d5677df4e93409949660fc4f46a35f54f.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 8 1, .triangle 6 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 491c85482b92119c5e9b942d405ed14b6dc71f6151bb6cbde133e18108fac6ad.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 495e699d79828f849afcd757d24c9e3c5ea74ffbb494d2979ba5434c045e75af.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 49742af3bf31f388df87307d898c70ca4398919d7ab4238a9a9d323dc7f9ee2e.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 4a9ebcbbf930f9ba8f44551c4fb1f40b5dae5e5d3edf0545cb60b6f369b4080a.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 4aca66045eb9aa2e4654038d61b6682c00441e2f9a2cbd76f5fd070f2ca2656b.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -3, 0, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4cd99188853bb199a3007464187a44cf514c7b3f5a21d4465fb664df1a2cf58d.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 4ce3a80fb3aa65f3fbf2b40ff0d36e2a5bd27fc366e6717a33de84c838843eac.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 26 1]

-- Cycle fingerprint 4d5d94ac3d6b3a55163406da66d9a41ce4213302c8dde3255bc0a4efa48dc23c.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 4ddd314b4507502516a5e05522723b24ae1c7c7e8ea2a7da0f98739ca87f6b46.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 4e0b07999bdfb8c8ec18410c3ce7dfff9a315239ba074ace947fbaac986a27e5.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4f4331e0e94fa3bfdff9a620ffc967e2f5081bce54dba537d04c86bf1bd6c7a4.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 53158baff503bc82eb97a4c39d0fa3371b52fd01d1b4b91e778394559e648c66.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 53b4ce8208e576e2f53eceb995e46f28e862ef7709c9fbf951914d0b66e57a8d.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 551a920e79ca1a522046853e92b262317268721ae50fa6ed7ce46bf6f1447712.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 21 1, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 556bef998e1f80d64095d3522f1c92a56973b510d579a1f372b6034929bfa067.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1]

-- Cycle fingerprint 55985d3f85d568fd30f2f7a73bc26be6d61753f5327b67cc8ef81a16cc2674d6.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 569b30e52e7966f3af74ac21176d25cc38ace401f7845b29999a5fc15db01d16.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 3 2, .triangle 7 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 58444ba9fe53c69fc27e599b181545b183797f85282f9168a5b7b133128ce4ff.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 59ce0793c46af2180ad3a93e3da07407a362da6476181cf18ca0f24084017218.
def localCycle00090 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5a4cb44b4e0bca14dad54a503dc3dbe84ad86f9aa7a9cf1f238cba8bbefe9fde.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 0, 0, -1, 4, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .gapLower 3 6, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 1 2]

-- Cycle fingerprint 5a91bcd0f60560eff0678e2cdf4a9a998a97da9845cb5bb73b07f06ccb586537.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00093 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5b7f589e3882b99020b1b9dd1f64b006d28bfb48b2161d05765b7c819ee4d086.
def localCycle00094 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 5baa6b7620cc7bd93e610946890be03440c65f83751186324fa5aed5810bf923.
def localCycle00095 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 17 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 5bc19d861d9beb29f5e07c2788d426e2b3b3c66dbbeb6b2bdc3eb1809921a254.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5c1dfa169c47d034d90361fd4d3d6183f62bf5dd87314fc48453d606c93a2149.
def localCycle00097 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, 0, -1, -2, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 22 1, .gapUpper 4 4]

-- Cycle fingerprint 5e52d4a29574d4be67238aa994a2d19aa218b52d823d0b396a16c6eb8243a1e8.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 60d4f6ef98253a3a4248d259488a69ba41543b4efc977ad7e8551b394aa3591f.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 61267542e4495e14c60e65c6827fc3add68a94525397c799a4e38a9a4d944d51.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 614c0f967f0e1579e9e2e2d4dde9b55406eb3f4e4b6d1b7680f12d8081f4f125.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 5 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 61cf3a509ba74b191e0b659473fa4da9738087ffb691f4ac4fe75ae7e0395795.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 4, .triangle 24 1, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 621e459341538a1ddb2ef20ab375f23939967c2c15001d0abfe2e84beab3034a.
def localCycle00104 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 62662e8c73ef22352267ea9c2b8077f949983084da2a6be6c6873506622c58c6.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 631906d683496afc13b99515f13840dda49ae2a363fc2de6ae003ac3efd61b54.
def localCycle00106 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 66067224ad9eda231ee0247493e0e080e4bbf34b206190d9d5c42c056a0c7b87.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 69320e9b41ce5e686b5dddeede9271376c9fe3cfe82f3178e7b623469f46f08f.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 0 3]
    constant := ![0, 0, 0, -1, 0, -1, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 11 2, .triangle 14 1, .gapLower 0 3, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 1 2]

-- Cycle fingerprint 69701726653b594ff4077360a6048af60baeadb2018d1a9bf7a795fc0e7d129a.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 4 4, .gapUpper 4 5, .gapLower 6 4, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint 6b96dc9807661df34c1f3eb9d9274a6265e7ba352d540592ab4871317368139b.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 6c027e9d0adab5781b918743d9a027718c0eb1fe29e2330f5211405c0d3fc1e5.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 6c15d0c27904f9086aca58c892be32346d5dca3fabd57f77a90e3af0774b8bdb.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 6c5348fab51fdd6b23cf2475c300c59ca37c71d20c9e5cc1f8f53a59f050d1c1.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6c76673ba5e64898338c8473825f0fda64156d7bc575097897ac9287e5915d8a.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 6cc10ff764e3e083eb8399071027cd5f36eb250ad085ea3e60bc489010d452cf.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 70634aabc32595c2344102e91ffa2d2dd40c68ec1eb2da9cd2e24f6985785294.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 70c6a2ec004e5d35194607c0f310befee3b146823e80da161504c6f640d41907.
def localCycle00117 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 5 4, .triangle 17 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 70cb137b6424ed95526e884ccb7100f32240e940dd3e054fadbf5528d7bd8e77.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 7249453cdd01aa93bc73a2bfc37ad4e7840f756a91253d87536cab865bdf90cd.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 724f89634feab4bf05357f39cf67700a74a9dc3b7d16deb3ad44263d48ff8f12.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 72eb9209d93fa3dc0ab0ba67bb919e2c08c6b6d8441560a96b4d44616e32db70.
def localCycle00121 : Cycle where
  length := 12
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6]

-- Cycle fingerprint 731131f7907aee96f74aa85a8f3aedc7cddcc5e5c82cb5dbb24975186b0560f3.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 73e968ddd20c7689088dd87e72421973ba523a10b30d6db0b3bf70ca9f95926c.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 2, .triangle 6 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00125 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 74d426a34afecb68e669c4c5baf0f3c9d20d8370141712452a0ab7250e1c7932.
def localCycle00126 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, 0, 0, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, true, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 1, .triangle 17 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 7907dbb898c1a1654b72142dee349422a0a3e37b4e024e9a9452cf210c2e35d6.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 794623e23f7876d2cea9b398baec81a95af9e03fc49512ce49b7533ca585e5b6.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 7950938288c675ad5295464ba5c6feea93cfd6a0f7aa1616fb3509373ac38beb.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 29 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 796e3bd8278f890f7707f85741ccd056cc6e6281dc457ffdf75828f21f239f68.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 5 6, .theta 5, .zero, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 33 0, .corridorLower 5 6, .thetaLower 5, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint 7a4bd0f2c0ec905379eb24a0d554780de075df9b27ab771c56635b78f826a585.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, 0, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 7abb8601372cbd27120d00109b76c25383976fe087ee09257fd962bd144dd5a0.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 7d87d0501efa9f8b7b780da09bfec37fb66de23b8c8e38f1b299b819a0bfc6db.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, -2, 0, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 6 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 7e93f5a83430233ad344fe05057651ddd02afe172b60cb0f0b7b2fecbdcc848b.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 7eb8ed8280dd9102ffb005c95c7a0744f8e28b9caf95375228a324ca7e6f3e9e.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 7ed828e4317747f39983a884b213b6057b9796a9bfd6bb735cffc57775e1cef4.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 7fed440a1fec8e3ab813c594ae8a58170010ac57ecf37b71f4636251f494fe1d.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 802872870a89126f95b2dd9707327959745db248617271cef6d872275ad41a84.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 17 2, .triangle 22 1, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 836637c97b5f4b07d6fb909022328b482943ea9a881814d86d52997eea90beda.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 83a4c0fec86636342d71f630f7bf6d5c59a2205f897d1b71ff1a558c6a6a268b.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .gapLower 5 0]

-- Cycle fingerprint 857da6d79773ba3d6aa8a445279683da38e4bb87fb2cad298e19bf28949d5676.
def localCycle00142 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .triangle 23 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 86674081e15f4c7cece48cefccca6d151c0e6a75d4b6cf74405d61d089ccecb1.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 4 2, .triangle 8 1, .triangle 6 0]

-- Cycle fingerprint 86f60f27572049e3efedb7eddfa4122fea9551d9b519c7a03b58147a6c8fa8a6.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 877f4b8ec78ce3773d0e3c4f52d493c38a3218bde130d09bb8cfc68e945f3fa0.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 884b965c8ec33451dcb13ff83baaa210a8732930af89efc74fe4e57e440758bb.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 0]

-- Cycle fingerprint 89480b731a0155c5d0ffbc2a44dee8648e5c26a11286a9accfe6022e4c03eda1.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 8ac6db43c1f225819d611de21dae1f0624ee295bee06407614a53d5e99cbc1f9.
def localCycle00148 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 15 1, .triangle 16 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 8bfecbf35cd89c60bc69a0d2d3acb2b0062cc0ac8d0fae9498aad5cbddd815ae.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 8c2882cc933e2b580d8e3e5563f3c496d3b57d555240470319abc86193a41b43.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 8ccc8c35aa6f7b24f44e916f89d3daa0d1ab5899969dffb8be76f7c6dad36dbc.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 8e13b6ca5cba9287ce29f8026d0d047dcab81afd7bda81db0773eb74e638fb5c.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 8ee6ff0abb97df3324f9847dc43d82f0f28b650d03753ceb1f672584863355ff.
def localCycle00153 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8f53591276318ab84c365d3d29838190374b5e05c42dbb511c490b86abfc9306.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 905024579f5ecd8f4fcf0512efcb015f21ebff0244b541fb719ca5ab7eec350b.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint 91341ad9d943f5a8a7048207ac454f38013a909b45d624b2f168ce54cc6c5351.
def localCycle00156 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 913734ca748d0dcaf334aeadc9b63aa5bd0666a4ba30df6eb417ecacccdd4a0c.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 91743b375a88238dd36bef3626c795264c8966f4f93df05f8e1ffc1885836566.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 9259ed4773ae3d116c20fb2d2c1f1a5730735c17f625ae8e057ee9522306813f.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .distance 2 3]
    constant := ![0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, true, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3]

-- Cycle fingerprint 938a6f12187a2882106619c804f94b588c2df38500420540cef74b7d69d349bd.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 93bc7036319b8d68c224b37a8600e0c981c754c283bafdf78c4be576c3c81749.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, false] }
  origin := ![.triangle 30 1, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 5 1, .triangle 8 0]

-- Cycle fingerprint 95fb0ced85a241e89dec7e07c78debe996e6f44a773c95ffc3758fadf5ffca0b.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 964a1081dd9e95049ce730850751f4623b04f6d13419674074f843e44f01ea7f.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 96bfb704c29fa0db3dc577ba1adf329b4c655d589fe9e7be720e65afc4ba08d7.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 98272faa9d859dea5ab0963e30cd5f62bbe1a5003afc72197c1d2671c2682d41.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00166 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 9989e3fade9db6821c1424fb9f0390b794a9096e3d2156e71e28c093c2b66570.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 9a02010050aa2653a814420097d0e492d4b3d492522bdb4c37d7580265999199.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9a052708b0cfb6a6d8d0153f15d9c27dc5764a57c19a9125347183a56735bb2e.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 9a2549ffbadff1598618480293565e3fcb2871fa2fdbd398fc5e686ec6260afa.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 9e3889d055b453e8176cfddec7ee7377d2239a672f3d87da3d07cfada8ecef2f.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9f52c23a9ffd9a482921942a2f656b16cd5d7e7b54cb6ff6b0335ea48dbbf27e.
def localCycle00172 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 9f763a901518418d7c72d035d5cfbe30b8482cb2146451fae1b071279f8c85ba.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 9fbc002c4e7cba2442451e834fa48f2313ba50eadf464b7946686da5c2806ea3.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 9fed990565f705302f20a40cc1ef137b0eb79437f1a8ba708b61a72efd8bbc57.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 2, .gapLower 1 3]

-- Cycle fingerprint a13000e2dabfc17e6c7df7b80c6cc7e600671d1db7fbc331f60881d91f1e52a0.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint a38a4bf2320674a22c40324b17c5b5937b1058911bdcf9ceb26d421ad588df76.
def localCycle00177 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint a410ebde39ba2a6972e6426ee55ce0b73a51abdb59f075263434e458434a5269.
def localCycle00178 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, 0, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint a4ee9d82a2cd6ef23b391805453eb3b1fd72866eda86072b4fa13efa9535eb41.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint a774a57eae688c8a66c2c167e1b33ad56088c5b3e6b4805e9d51bf24475334cb.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint a79e49cb04296bceaa3d1474a847cccf44cd0f50039790e9009f696156e7cdf3.
def localCycle00181 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint a801ccefaae61cdff6fbf8f3ead579f7253d490bc54447f55d2010a9d99a283f.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint a8780ad01977910a805f97d14e69130909c0f03b6cfb8e6d0c76a89086fe084f.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint a8d81af7b0b2f4def38823540cf7f884168e5e74ab825b6185855ea6017d0d9e.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 6, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 5 1]

-- Cycle fingerprint aaa5ebc7b2a307527ac119f732d4ef1ce8cb54462cf11832e7800f4dd9e1c898.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint aafaf47796ab5f6bc38ca7369937c72daad8f08bc80d09ec7fd3a8ca202cc33c.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 24 1, .gapLower 1 3, .triangle 0 2, .triangle 6 0, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint ac7c67054386444a09e3d283ec8ec1c503f408ca61a1dc4a09535002c239470e.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint ace046a80cecbd69a38bdf81a9161c1d4fd33a3e46a8bc05d3480eca8b5eb8b4.
def localCycle00189 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ad3727239391dd90e198e1d958c2945ed949fb280b94a29c6a1e76d58472448d.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -1, 0, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 21 2]

-- Cycle fingerprint ae334c39051365a3c58196eb8b411d4a9006798ec1ec6a577dc01a7e904f48c5.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint af2123de171863b9376e3b786def98a681b4bde52792da638fdc6cffdce24803.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b0f9a504f4a2be259fe7310fb54058f9076e19b9225a57e2797c8859260d2c1a.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint b1a5f725cc91307e8878daad8f458e52310c897490c400fb1d44b2a920ef8a56.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint b27ac98d45e601161f0b561d1658eb6e726d7cb7243daa356152638c6f9203e6.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint b32a5d4b7114a22c2e4a6a23d8174798010c0774c533b7e25d6d79202986cd26.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b54b58098ac07d6ae74a9d3ca4a3f7fcae4ea77c0b105ab8516e3d0a5c7b7c16.
def localCycle00198 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00199 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b8a2afb31e3d5bdd2c81362f2ae718cfc844e285f3418ae430485f27de9490ea.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint b8dc67bddc91aead95f9bb43e88ac878fb79786b580ae2864bc88a703b17cd77.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b8dd2d9222938fb679caf3fc1d3541ad0c68ebcd6e89f51eca7c29d8c2b7afe2.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b995fe21c7dae8028bacb04d55b1543c939d819ae411e7e7ce8f799d364fc3d2.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint ba5f436c642ba78e0ade877dd7bb6f95094f13f9a38993de5f7acfc8c3f99431.
def localCycle00204 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ba7378e0b68b247b258f301e7782f48cfe4cdae2247c1619c3edbb0908957945.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bb26cf28891d67f290fa8ff2f6bbd62b8ea8c421697484a20b16ed981b2751e9.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint bbda9a6aed76a4956d87de271c71c05d20c5df3d4652c02b01e6660fd0cd1cd3.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint be959ca8f87e201c605a0f70860e756da5413a523c7ef839b6edeeddbcd92d60.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint c5a482e4037bd3889fe49954f1eaf81fa3a3cf86b637b188bbafad006d63666f.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00210 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c707a6ec38f12f264e70a1945f11bea0f5977b0723b958028942bb9676f32839.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -3, 0, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint c898c4c4d58d6f807c88acbf6c70f3342f30a40bed97904ef4f1db08fa11e954.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint caf42417d449d58befc1b14a8dff623b59bfe86e1d52dbef817b1cbf2c7cfe6d.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint cbd453b2cf674fe0802a4de8308d70488a53c0cde517fcdc5e31cada6ca3dcd1.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cdfc5281a5bbbd7d7002c3f06a78b85d0d48b65ca9d1e7c0824bdf4d1b6eeebf.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 18 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint ceeac007e830572efb1bbded8dda5c399fd343c00e110a09c88fc12554d3fbbb.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint cfd7bd87ecaad83f86e3c9090da6b52f28ba53daa43261ba10338460cc7aa4c4.
def localCycle00217 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint d0c16ffbd0a1066eccaf4e58901d364ec429c88169cd70b67666bdbbd58b8ef4.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d1b8ab37884d7ecab599a430e1fc167b78d91a9b759c46ac72c583fa12315c33.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 1 2, .triangle 5 1, .triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1]

-- Cycle fingerprint d1d05e844354705e850575f7e40df910ef04b7dfeb6c58b7f4285ee4c4040d23.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint d2b48ceab5ff8c87a61df6b4a1f161babcd993ef0537a2617d825956e5cc9f59.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 5]
    constant := ![-1, -3, 0, 0, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 2]

-- Cycle fingerprint d3bb6ed567ec7cb9ae5da7fae133c7e329d5b121bc66cb7abd6acc47b6ded62e.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint d458713f2476c9bc16bcaaecaebfe1294ac2dfdb972d5822d807d8c25c067ad1.
def localCycle00223 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d54e2c63738432b8a90896b8fb742e5b33df096451283cad641fd711fe28737d.
def localCycle00224 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 4, .theta 2, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, 0, 0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 1 2, .triangle 5 1, .triangle 6 0, .corridorLower 2 4, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint d5eddf6fd156e5dff85e4e4dc130f90532d44cef35afff4b15ddcbe82025ac4b.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint d7a5ccf3021c556bf75123076ec968972af52f3c2e3a59cc8c5b699a6b302a15.
def localCycle00226 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 18 2, .gapLower 1 4, .triangle 17 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint d7cbec7bd93fd3cde380a1e0ba730e68d77c1344caf19c528a60d647387a44f1.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d9f6a4a0bcb3ebafcbba16a9e637d6d95add704f839d64ce42df0074c9742bf3.
def localCycle00228 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -1, 0, 0, -2, -2, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 0, .triangle 15 0, .triangle 17 2, .triangle 22 1, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint dcc8833d3a426eb225cb090a343031b31410dff775b1cb864cfaf7b7f1f50354.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint de2a9151dd6b21176d29b29a06be3f1c507eb31acea61e6c9b2a5d3b65f75ca4.
def localCycle00230 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint de4a1845900c09f6df105da9c94ee87edfb34bf4db2c1c0e8b9114b8c4563450.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Cycle fingerprint e1493174da1f772fa4a189440b3303d00f53437ae8493ac193d47b5872400239.
def localCycle00232 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .gapLower 1 4, .triangle 17 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint e25c4fcc6b36ca05adbd3f1de47b5ffecb7c012113092cc4e18755e938fe4815.
def localCycle00233 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint e3aea787839f5eab33d6ce6eb34f6b3c190893faef27be89c5d73ba8212e4618.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e46a6feadcf1c164a22c538c56e53fa29a85244b8606c0a54795c6f2c91bfdf7.
def localCycle00235 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint e5b2d367b6c678595d329b26da1f5553f76f3dea6a186623b22592dfd9a2aac6.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e6b3d513810e259163554e367d499ff97bcac57db64d1e1b698bc26b08fe2bbb.
def localCycle00237 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e74c1eab802b66ed7ffac390e03fef04b8bd18bec9abd03671cbd04844c78006.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 3, 0, -3, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 33 0]

-- Cycle fingerprint e83e043e582e03bc3141c4dd3fc0629c3195d075e1bbf2e34dc0096df19144e1.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 0 2, .triangle 7 0, .triangle 26 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e8b10b23be96a769ab2c2778128b06026c372c0b716e3e20e70f96f0bc52c9c0.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4]

-- Cycle fingerprint e93fd13732310f0610ef5717c470833c8aa9e984f03140a404fda699b20aabff.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 28 1, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint e96bed7567741e195a3eb8a794e0b10568d3ad79e720908c19ff8ad803495fd9.
def localCycle00242 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 5, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint e97c5acc5f6eaf8e77aebcfdda5acf83e080cc93b740ccd89a40c1552c8a66ef.
def localCycle00243 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint eca8dfc61c3c2f2e8d567b9e1a1422591b37bc0617f949356a7bf83526a1497b.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint ef7eaafaf6046c7781c55c41b66b0105691a6f3318817e29f75a9501237ddef3.
def localCycle00245 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint f10f6294ac1651b084e649181de3da4d98573a1e6592517c0110e24afeabb67d.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint f1730cfe4cc2ed8d00097898db41ecbdebcf97e7719d043fb6ad3882be853c55.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint f2e6c1af0eb5ae3ee9e960ab6e68768158cfa525a78eeaf454234ec97d7b3b02.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 2 2, .triangle 6 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint f4c18c9e11faa4e74735d71e9b2e51092bc28ab36c6140edb3892c5646d20878.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f4f4088a5aef33e2c321decddbe13ab171bcf82f24ddc66edd5837a218a0c289.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4]
    constant := ![0, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 2, .triangle 8 1, .triangle 6 0]

-- Cycle fingerprint f65263e819dee6f1cd4565f30706407f82eeef56c20505c84152b6203c91e9d3.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4]

-- Cycle fingerprint f6c344930ef64025f0ee936ce8a1c60a19f67f5aa8c9ef3573ff4c6f40e58ebe.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -3, 0, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint f7212fc885abcb77c4a4963f9f134827ac36a9bf84c8a04565fe5a6b53f8834b.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, -1, 0, -1, 4, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .gapLower 3 6, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 20 2]

-- Cycle fingerprint f7a2423bac1716e4f25c009a98cc2a8df627a4236b267f697ec6e4df7eccb848.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint f8aa71617abf68428b420122773eae5115d42064019aa3fb19092b4218367002.
def localCycle00255 : Cycle where
  length := 11
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint f8fba185886513e08a5db029d469162a4a7a1730e0d3148f228a644380939925.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 22 1, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint f90f6622fb35be7a9d6483cf1c295c176a5a35130c5ec3b65c7270827d4dab7b.
def localCycle00257 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 3, .triangle 16 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f9fc66599e8cb464a4cffcf3e0b29edfd8425806b66ec4eaa116ebf113b00f24.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -2, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint fbf8bdc85b80422860927dcf852792628bfc83d8a53b93beda2169efd771e26d.
def localCycle00259 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fcab0b37e5a31e453f05a695b900baba2660f4985283ab780b86f99dda04d57f.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fd99f7e7e17e150d60be77493afff7867319fce0fa5115b1c810bb77f9381920.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 1 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint feaede41be7c845b3d09a5281bb61a1b6f4e4a171ee6355167709a57efc7864d.
def localCycle00262 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint fef5c9e8d1adad2d29c8b4065e9b3a5cf1384fc8f8da6da77044058e743ba8a3.
def localCycle00263 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint ff9426c0affde46d7a82ad842bf798419fdc6ec90a61c13dec4c2689e5965888.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 4, .theta 2, .theta 1, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .triangle 21 2, .triangle 24 1, .gapLower 1 3]

def library : Library := fun id => if id < 132 then (if id < 66 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 49 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))) else (if id < 57 then (if id < 53 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 61 then (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))))) else (if id < 99 then (if id < 82 then (if id < 74 then (if id < 70 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))))) else (if id < 90 then (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 94 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))))))) else (if id < 115 then (if id < 107 then (if id < 103 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 123 then (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 127 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))))))) else (if id < 198 then (if id < 165 then (if id < 148 then (if id < 140 then (if id < 136 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 144 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 156 then (if id < 152 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 160 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))))) else (if id < 181 then (if id < 173 then (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))) else (if id < 189 then (if id < 185 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 193 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))))))) else (if id < 231 then (if id < 214 then (if id < 206 then (if id < 202 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 210 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))) else (if id < 222 then (if id < 218 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))) else (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))) else (if id < 248 then (if id < 239 then (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 243 then (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))) else (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)))))) else (if id < 256 then (if id < 252 then (if id < 250 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none))) else (if id < 254 then (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 260 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))) else (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 5, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 156 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3840)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 2, 3, 5, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 3 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3841)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 2, 3, 6, 5], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 101 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3842)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 2, 6, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 169 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3843)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 6, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 110 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3844)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 2, 6, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 227 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3845)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 0, 5, 1, 2], ![3, 6, 2, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 75 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3846)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 4, 2, 3, 5], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 0, 5, 1, 2], ![6, 3, 2, 0, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 119 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3847)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![118, 262, 27, 59, 194, 224, 250, 255, 25, 233, 122, 43, 199, 154, 257, 163, 148, 245, 117, 7, 95, 95, 121, 253, 186, 153, 71, 65]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3848)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 90 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3849)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 140 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3850)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 243 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3851)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 3, 6], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 94 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3852)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 201 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3853)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 243 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3854)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 222 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3855)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .tail 208 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3856)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 28 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3857)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 135 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3858)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 1, 2, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![146, 187, 27, 59, 225, 143, 108, 123, 22, 233, 229, 167, 10, 6, 39, 100, 70, 139, 117, 95, 95, 95, 149, 83, 264, 235, 19, 76]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3859)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 5, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 2, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 204 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3860)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 5, 6, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 1, 6, 2, 4], ![3, 0, 1, 5, 2, 4]], proof := .tail 157 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3861)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 1, 2, 4]], proof := .tail 197 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3862)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 1, 2, 4]], proof := .low (![40, 132, 9, 263, 213, 238, 0, 51, 105, 217, 134, 4, 10, 106, 180, 260, 4, 160, 82, 106, 106, 106, 120, 182, 175, 114, 12, 223]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3863)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 2, 6, 5, 3], ![4, 0, 1, 6, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![40, 132, 9, 263, 237, 159, 261, 51, 105, 217, 134, 23, 10, 106, 180, 260, 173, 47, 82, 106, 106, 106, 120, 182, 175, 111, 69, 130]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3864)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 193 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3865)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 28 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3866)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 28 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3867)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 1, 2, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 198 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3868)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 135 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3869)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 0, 6, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 202 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3870)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 37 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3871)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 155 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3872)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 231 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3873)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 0, 1, 2, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 45 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3874)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 0, 1, 4]], proof := .low (![236, 254, 125, 221, 80, 211, 261, 247, 24, 42, 113, 63, 10, 137, 96, 150, 116, 47, 35, 84, 81, 248, 249, 220, 258, 79, 129, 31]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3875)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 50 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3876)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![4, 6, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 21 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3877)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 45 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3878)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 2, 5, 3], ![6, 4, 0, 1, 5, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 0, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 188 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3879)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 151 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3880)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 53 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3881)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 165 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3882)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 165 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3883)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3884)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 56 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3885)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 174 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3886)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 174 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3887)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 107 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3888)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 60 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3889)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 2 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3890)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 60 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3891)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3892)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .tail 56 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3893)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 174 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3894)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .tail 174 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3895)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .tail 107 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3896)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 60 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3897)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 60 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3898)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 16 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3899)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 2 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3900)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 60 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3901)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 60 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3902)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 14 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3903)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 212 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3904)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 212 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3905)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 212 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3906)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 62 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3907)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 52 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3908)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 52 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3909)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 144 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3910)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 62 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3911)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 205 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3912)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 0, 5, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 244 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3913)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 3, 6], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 48 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3914)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 101 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3915)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 4, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 41 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3916)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 5, 6, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 32 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3917)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 170 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3918)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 34 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3919)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 4, 2, 5, 3, 6], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 200 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3920)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 4, 2, 6, 3], ![4, 0, 5, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 101 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3921)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 4, 6, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 41 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3922)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 5, 6, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 32 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3923)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 170 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3924)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 5, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 34 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3925)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 4, 2, 5, 6, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 2, 4, 1]], proof := .tail 200 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3926)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 2, 4, 1]], proof := .tail 200 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3927)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 4, 2, 6, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 0, 6, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 101 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3928)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 2, 0, 4, 1]], proof := .tail 177 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3929)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 177 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3930)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 75 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3931)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 4, 6, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3932)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![4, 6, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 227 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3933)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 75 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3934)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 4, 2, 5, 3], ![0, 6, 5, 4, 2, 3], ![6, 4, 0, 5, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 119 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3935)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![104, 178, 29, 68, 172, 91, 218, 228, 195, 18, 26, 43, 199, 136, 189, 232, 126, 181, 109, 230, 58, 57, 127, 54, 168, 15, 85, 184]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3936)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 141 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3937)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 102 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3938)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 13 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3939)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 196 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3940)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 3, 6], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 102 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3941)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 13 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3942)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .tail 196 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3943)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 4, 6, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 209 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3944)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 5, 2, 3, 6], ![0, 6, 4, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 0, 6, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 1 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3945)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 0, 1, 2, 4, 5]], proof := .low (![128, 187, 29, 77, 166, 74, 219, 123, 259, 256, 171, 246, 10, 214, 112, 164, 70, 139, 30, 162, 234, 124, 20, 98, 88, 72, 241, 76]) }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3946)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 2, 6, 3], ![4, 5, 0, 1, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 0, 1, 2, 5, 4]], proof := .low (![78, 99, 210, 147, 138, 74, 92, 38, 36, 251, 240, 246, 10, 215, 112, 226, 70, 190, 55, 142, 5, 5, 8, 97, 97, 72, 191, 76]) }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3947)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 196 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3948)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .tail 196 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3949)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .tail 209 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3950)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 5, 2, 6, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 0, 6, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 1 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3951)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![128, 187, 29, 44, 86, 242, 161, 123, 115, 33, 103, 185, 10, 152, 207, 145, 49, 139, 89, 183, 158, 131, 192, 17, 61, 73, 87, 179]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3952)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .low (![252, 99, 210, 93, 86, 242, 161, 67, 36, 33, 103, 185, 10, 66, 207, 145, 49, 190, 133, 183, 5, 5, 192, 17, 61, 73, 87, 179]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3953)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 1, 4]], proof := .tail 206 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3954)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 1, 4]], proof := .tail 203 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3955)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 176 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3956)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 1, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 239 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3957)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 5, 6, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 4, 1]], proof := .tail 216 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3958)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 4, 1]], proof := .tail 216 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3959)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 176 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3960)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 6, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 0, 6, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 216 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3961)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 5, 6, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 4, 0, 1]], proof := .tail 64 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3962)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 176 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3963)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![4, 6, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 2, 6, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 64 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3964)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 46 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3965)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 46 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3966)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 2, 3], ![6, 4, 5, 0, 1, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 11 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3967)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3840 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3840 ≤ id.val) (hhigh : id.val < 3968) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3840)) = true := by
  let j : Fin 128 := ⟨id.val - 3840, by omega⟩
  have hsum : 3840 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3840 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard030
