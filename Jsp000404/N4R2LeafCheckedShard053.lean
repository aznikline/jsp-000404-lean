import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard053
open N4R2RowDataReplay

-- Original cycle 034f2043f196e3164488133305ef192171472013c33f42284a328621c7bac50e; original global index 266.
def localCycle00000 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 3, .triangle 34 1, .triangle 14 0, .gapLower 0 2]

-- Original cycle 03ee1759d05f5e5a7dd06cac234db413b5a33b8f518e92bd9cf1acacbe035da2; original global index 312.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0416cf29e712a6f83c6c69ed11611d0cf7218e9cd2ed58a03b909b45b3babc61; original global index 322.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 042884d5f59ef95284e265f760327336a46cb91f29f97d6cf532b75e6967a909; original global index 327.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 044da34d14a432942e976283581782ac2f186aa36715264cc3301f53b2aaab6b; original global index 338.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 0688d67877798053eddeab526993f201b6e9793f127d30dd578da62e70611e7f; original global index 537.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 4, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 070f004c7a16f9d473c9cb2f1c21d8f46f2f35bcd7c88a962ab376c03dbc40be; original global index 579.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 086e587e8a6e8741ef8458ed28e092297959be4ee3805d02ae450c493c5eb877; original global index 671.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0969158a0ec6bba55d051e627b6f9a2db02dee736620566fb6c9718f68fb40ea; original global index 748.
def localCycle00008 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle 0b798086f5e2e3f9d33ebc733fd89fdff1b04a7f7f554b6d0ae2ac555de357c5; original global index 923.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .gapLower 0 3, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 0bec130c410120f2448700eca0c2f1e8879013b390bcb96e251e1637b5adef19; original global index 947.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 14 2, .triangle 11 1, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0ceee17b63aaa90257f690f1de553e85dc00e7aacc26995d67d0768899393f1c; original global index 1019.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0e96f8e11a1542223cf65957455fec05fa2494eb739859c7b3b2e993eb618509; original global index 1150.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle 0ef6b8aea6f22549c862823e67accb331753a5f8911a22e13f354289876fce21; original global index 1184.
def localCycle00013 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 5 1, .gapUpper 2 4]

-- Original cycle 0f020cf664e328731ffdf6e1ad30acd96d4e2157ce04221ff6e3c1acdafeacd6; original global index 1188.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0ff3faa70de8787cc93d9da57e9f4e120aaa30f707a9ea777400832860ab4297; original global index 1272.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 10ee61e576a4b2222dc72fa094e1af5948d5e382361d44a1da5bd9849aa57250; original global index 1359.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 1164a3b713317fc8045a961a2f06f2230f9b9d7a00bedb46c612ece5289db215; original global index 1385.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 3, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, -1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 12d6f3a94c7f8e96deb2562900312ca4cb51b212a546ecbbd2fa5574a361eec3; original global index 1483.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 2, .triangle 12 1, .gapLower 0 2, .triangle 13 1, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 1564e71d346d5c2fb62a98f5b892764524728c66cb1899b1262069f952cd66aa; original global index 1690.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1743a9960acb62e7ac74eea6956c42985880173e87f8e60546176c59a7c55daf; original global index 1830.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 17838a7a9c544f54043a726cfcddd2c2eb90585d77c2e3906d7091583850923b; original global index 1839.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 17b17d663ce14e139fe1a42020505d20c0958b65c6bfe1b07acaeb728ca5ed84; original global index 1852.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 1874005b9ab5c9f133ed6b58d2b6a89535d4d4741074b564da795405dbdd67da; original global index 1915.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 14 1]

-- Original cycle 1931668b71f8a64aa37c5794a6c0cb32c283a3e440de643a7f9c80dd3318241c; original global index 1966.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 19350bf6367269a0cc7a7e938439e236b41715794366b450e72bd7064102de39; original global index 1969.
def localCycle00025 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 3 4, .gapUpper 2 4]

-- Original cycle 1b635bf724a0ff3e106fc5a1107adfaa39925d1276ff39f4554774b4990a5528; original global index 2122.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 1be8afe7f66e44887903116af5aafccae36fa50df33d9a2e9fb6374fc30426c8; original global index 2157.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 1c88bdf07bc92aab001f1996a297735887c36fb51fd8bf86534b9bdbd41cb3e6; original global index 2194.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1de55aa9c3a835414ddbcc32fe1c61ddcf1507fc1629d1b7995ce588dfbed1e6; original global index 2297.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1ecd772d78fcf28869a80e1e257c7e9e786efccb9bd6430e7ce89ecccb433133; original global index 2364.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 29 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 2146b5031631d2fc05f151d7a2240ba8496f9a3b1a05394b342ac0a3b58476b9; original global index 2549.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .gapLower 6 2, .triangle 27 1, .triangle 33 1, .gapLower 5 0]

-- Original cycle 2174333ab4d9bafb42d362480b46027bf397f749f9f1227a5b5a74189f594c1b; original global index 2560.
def localCycle00032 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 30 1]

-- Original cycle 225e125a4bbb8ead1bd841b0ddf62455b859a30444288c4af377e39e9bcba32b; original global index 2633.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 3 2, .triangle 14 0, .gapLower 6 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2346813da69a59a9ffd307c09b17e0df90abeb222ff76ac0e85de7b3464d0257; original global index 2703.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 23f95e517257a2bb93541bfded2f8a56cc3620857ed1870d3fd32a5d67fe2067; original global index 2754.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 2465aa106a2a2aa1282d6c6be4e531f83fc6b27d49fd3b92374891628e665691; original global index 2791.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 4, .theta 0]
    constant := ![2, 0, 0, -1, -1, 0, 3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle 253ecac2fa450b65f908875ec1a0c853455248ff9c9834cc3eea0cb48f6d4f13; original global index 2863.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle 27423beadcf6f506edc17faaada85323935b7a0209b893e1f319c2e12b3c5c6e; original global index 3004.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 27dc6186fba271e39da46048a3b56b2f937452187f8554762486eb52da67b0e6; original global index 3048.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2825c3c6d9571bd01c5f26f4ac7c64dce47f35c3edf8ef1239a8e1b1c7c273a0; original global index 3070.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 2867de0d1390482ebc225874c4b7cad5d6b9cc618f946f4cf2cc62852a409a2b; original global index 3100.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .theta 0]
    constant := ![2, -1, -1, 0, 0, 3, -1, -1, 0, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 5 0, .triangle 27 0, .triangle 33 1, .gapLower 5 0, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .gapLower 0 0]

-- Original cycle 28788622323f594890061fc9509a4e02ba6f8f1aa9cf6e423f67e321edef6a96; original global index 3101.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 2955b56eaebabf9564f761925f8b06d16e744991ab30e9bfe8edb540adecb562; original global index 3154.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 2988f8140b669fd7c49801b32baaa171ab647d4777b6c6a153e1257762921317; original global index 3167.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 2a740fb6f262f4ccc56a1855110c321c7429d6bc6e4ef1fb753b12b1ac0d2ef7; original global index 3237.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 2cd5f1da5b2521215b7d84496e1e8549b2ffb98e577cca4e43ae0da2a49cf0de; original global index 3424.
def localCycle00046 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 24 1]

-- Original cycle 2d5d28ada8e1d5130547b8d0a22d145db602f271b4db0cbee18b60b25b24951c; original global index 3461.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .triangle 27 1, .gapLower 6 0]

-- Original cycle 306e0a9bb9e91aa05f84168bbbb69e71d1347cddfeca85dfb3e6f970713202f9; original global index 3686.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 316730064d5aa87265c741f63788a1b8c12126032c413112f0aa8458a1c6eeb9; original global index 3767.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 33992534ca4ce2ca479fbf90af25d67fd81b9f3d103aa6b11ae505013ecf8c1b; original global index 3947.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 2, .triangle 12 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 34362967c3a28383fa6a6ff76ead39386835e57175c1136fe71a6058b0ce1ef7; original global index 4001.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 343aa5a0b9e27600979484aaf61c52d801966f834da4d38c6f873ae2eefae432; original global index 4002.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 5 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 3607035ea4ae8259e510926c6fd2412935bb8063515f295df22834a2a8f8ce90; original global index 4148.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .gapLower 0 3, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 36748a96d879b8e1a1cdb41f4fadd70f0be6c6564d1962271ebced3556a33269; original global index 4182.
def localCycle00054 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .triangle 13 1, .gapLower 0 1]

-- Original cycle 36959ba98b0a4ba2364fdb4360d997353065027953a60f9790d68b2a1d5473a8; original global index 4194.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00057 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 39bd2a5aac17e3ce33500edfc118e3e8113a9d550f6797eb96bd5ae5591562b5; original global index 4455.
def localCycle00058 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .corridorLower 5 6]

-- Original cycle 3bcbf61177e772c6792ddbfa05385ac396619153a485a49fe6abcffa08324aab; original global index 4626.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3bfb26902e72f2fe3fa475d0cbb270d8e6a2169c620b9b051a08dcf468bd26d4; original global index 4648.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 24 1, .triangle 22 1, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3bfc8fb7e3207a28a49f912448844395c13012acf7cc0ba8ec925d4eed9987ce; original global index 4649.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 3dd2e6633dcbe596c87ce23befc9334ed9d7ee830c4bbfb6be71c11e443b5275; original global index 4786.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3e55139de6387254a2129ab5b893f4616fedcf418b2c3f7002489181eaf5e0dd; original global index 4824.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 3e9f597403ca8b56d627d80270c02053434ee7d9da3f338398f31883ee62e4a3; original global index 4845.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 3f38e57884729131554e00d86704032084a832f9207d9edc7a6673530a8e2932; original global index 4882.
def localCycle00065 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .gapLower 0 2]

-- Original cycle 3f67b04c63200a92652e7a500db4cb95137f960c48372740b5153b86b128845d; original global index 4896.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 401eae5d61a31ed16b3a6a992998f7b1b906bd9ea2fea42a6b33898d3b4b6dc2; original global index 4947.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 403ecae26e33a129517bd942b58e5fc2c5e1337e7b8cf312e7c86a3e87c8dc69; original global index 4958.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 43b383c9433f88ae88396eab9c05d38e8b6c3889d303f8d996aab13f3f8b6d17; original global index 5239.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 445b708c05a60c2ff38fcab7b4f4c2de1685d0a890bbc3b15612acb2bd530900; original global index 5293.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 447ab8cbb7d14fe72eeacb1869a2850759fe7347bb7c84517887185615985a03; original global index 5299.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 3 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 45acc262783fef7012c47ffbffe5c7a27f67f579f2421051940e1e53453a6eaf; original global index 5390.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4615a2961937dab67a10fdacd9ff1c67d326b45a40f0498fece9921a9407b21d; original global index 5426.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 1 5, .distance 0 5, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 24 0, .triangle 3 2, .triangle 12 1, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 471a1c67cc7eec5409429a08acc1138bc87f5239c588af75e731cf559df145ec; original global index 5512.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 48cdbf9da146262244058d52419d4f6f1df85a3d8379b32b28a5712d7fb311f5; original global index 5640.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 48d68656082900bab1afd2421945bd1cef7c8624c08b183d16f2da4c6632ff25; original global index 5643.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 4bcc79991d7204b14546beb0cb3f544f5302365e6d04888bb6d2e38e43a01b41; original global index 5884.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 4c082bcaf7d97b7aa747cdd28d5873f66bb4c2ded2c12eb7df3dfd00a73e663c; original global index 5900.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4cccf2159c3f0938c83d98918f5e42e9246aa377a6db15b5510f60cb986c72b7; original global index 5961.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4cd2b4b2766822da1cf8eefbba28b591bdc3e7698ea8ebccaa0ee50bcdbed19a; original global index 5964.
def localCycle00080 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 3, .triangle 12 1, .gapLower 0 1]

-- Original cycle 4d42d5ffd24c0b74b4ee019a093ade194a98f4f0980bc1cde62c9d8545098769; original global index 5999.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .gapLower 0 4, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle 4d72eaf9510a51e32cd6a0243718a6465b3b29a1d1bfcf18a7bcf041b696f74b; original global index 6012.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4eb294da3121e66f3b614d6a3526fdf85a8f3b2264c2d0d4e3767b446fc7710a; original global index 6116.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4f5e2d64b6b0451fb27f3653f45951995ae2c092713c1f307f68336e03bab4e1; original global index 6169.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 8 1, .triangle 29 1, .corridorLower 2 4]

-- Original cycle 50a07d176b7fbcf1c3cd211f34afc544f6eb3b5ff2a0a3930157681970d088d1; original global index 6259.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 513f0eb7a92de791d94a1667968b2a75cb250b32cf8684fcc8e11cd0c2574e45; original global index 6316.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 51a32c21c8cd2f5e7d9acf1799dffc4abd826a5e86b53473ffcc7affb3c44d38; original global index 6353.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 532aa438ebd866a9370fcf3be32bceb5e4a3ad3e95c5ec0830b01f6a39523c31; original global index 6471.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 53d66ba16da67aeb1fa80c76d45eb692599a22352d33afcb58df45a75e544295; original global index 6507.
def localCycle00090 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -2, 3, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 56d1463b1af6bc07120582b6b6db50f7f2345fe6ed7a76053a0a8cc5729abe41; original global index 6728.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 56d5b24bf1fb99cab6a34b8b7d5869522a45481905d71e6784251034302747a2; original global index 6733.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 56de815f53343e273bfeeb2fcbcc1371d3405fd3d1a69412a32470fa8d7ee0a5; original global index 6739.
def localCycle00093 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, 0, 2, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 4 3, .triangle 34 1, .gapUpper 5 3, .gapLower 0 3]

-- Original cycle 58375e445f6c56ceb754a811935f8f0fafd402a66b8d94d5accb9c2c3fc7413b; original global index 6844.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 594b1d628e30eb07b9b46d55da3ac364d1e8b1c93e3a214948f893910f834e74; original global index 6929.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5a42ea17d93476bff93fa56d2bcfa7c2bfdef170548be5ceb7eb75076a406e76; original global index 7022.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5a9ea8e0ce3312c3556b005663141cc7bd88a8277a28f32285e3d320b037c7ca; original global index 7053.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5c298ab48add7a660ef9bec979cc2df0ca4f19deb8f49741b1ed2652aa7afc90; original global index 7176.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 5d6ec974b29cd2d0b4f34aa1b7accfb1f4fd231db4e1adff4249ce7bc1edb711; original global index 7273.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 5e07a6ad9dd0f31ff7a3e8c24713311cdcac16ae63a84263e9bf312b07e15650; original global index 7311.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 5e6d4cc2d589bd9b2c88770d504f162dc879116d7311cfcb6452da5512ffff28; original global index 7348.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -3, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .gapLower 0 4, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 5f41cf0db09b7803c96b7a4e1b31369a0cdfb1e68fb20a7ea5e0255da8145348; original global index 7415.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 5fcab7f7d149f99e912b258d13231c88586d4f8b81fccce6f25fa8bd5698c4a1; original global index 7467.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle 615f3e8cdd1104a90589d1862ddba1d6581f1d54a6f0e99423a57bf075c12c80; original global index 7593.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 11 2, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 616513a0de667fe838569324ecc18312aaf37e4f69629e07dc967bd00f6d8d4c; original global index 7596.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 623f5e9189580c43dfe3425a418c55d4872dc738ad099075a8518bf5e4b3e38d; original global index 7667.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 652e1767cbee28a79c553476f0c48a73340b2d2b23fbd455ce39d6f69a36945a; original global index 7872.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 65cc3eea041876140c68a041b37b607eb87efe3a008cb2cdde13d236c1347585; original global index 7922.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 65cd407dc1fec7d2c5e77687af4096958e5417daddd52473b83e4043b54022e9; original global index 7923.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .triangle 29 1, .corridorLower 2 4]

-- Original cycle 66a4271cb5686b2db047f1b458cc2eea9600ccbd5bac112397ef11c558cefaad; original global index 7977.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .triangle 4 2, .gapLower 6 3, .triangle 32 2, .gapLower 6 0]

-- Original cycle 67335d407e25d404fc8d983c9f88f5df36d66f094e37cffa7a5525acbb9bd1d1; original global index 8022.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 67458f8dbaf3bfbb7c7a618bb4f3eac06c5de0be8a546928ea184b68e0103781; original global index 8028.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 6820a877fa205a05e4ff95e11a1030fc831603d90bad3447052831996987025a; original global index 8093.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0]
    constant := ![2, -1, -1, 0, 0, 3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 0, .triangle 27 0, .triangle 33 1, .gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4]

-- Original cycle 6833321d56ad812f31023eb420040cb336a304eeebdb4a04694d8bbf8343394f; original global index 8100.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 6882e03b61ddfcdbd4ea9f55cc61269f5fbb6e5d1e786723e0d28963714de2e5; original global index 8129.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 693e98dcff37a1287d54120ae4696bb163580645deb13552ecf000836536543b; original global index 8186.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 4, .triangle 23 0, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 6a2fa30a48b31f3db3cb6f74d2883ebdbc1f0e3b1db838a0259c7fbf9b70e9ec; original global index 8263.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 6c0bcd061a4784fe0676f9544693d1e5f09f97ee9e463e99296d8aca4ce4af3c; original global index 8420.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 6c0d3bb4d61c05f98b51aea6870996c78ced730a68dc3bb997ca245adf7775c2; original global index 8421.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6e94f6bb9067c80cab2b12473ac0e78f85b309c3fd116f83fa06114822067472; original global index 8581.
def localCycle00121 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle 6ea78d46749c24bf694f030e050610917eccc411796e7fb49bbc34b6d5da176e; original global index 8586.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .gapLower 6 4, .triangle 32 2, .gapLower 6 0]

-- Original cycle 6eccb4376561ff6d1a18d0bdd153068af47bb3c055e3c70a2842a2f5bab2952b; original global index 8596.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 700f853b4871a8c12b952fdad2d82d186aaa5ae00ad4d4882c1cc1c3993c94af; original global index 8685.
def localCycle00124 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 70bba30de177614fd786012efffbe4f3efb3b3a66c371c055490c2615c494e0b; original global index 8738.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 70dc4c64dcd8345c12e74689eae12b91dc360652e4ad06243ee8a828625da85d; original global index 8745.
def localCycle00126 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 718c2533fdddd83f208f61739ef506694e974f82dbef55fb5ad01079d552e091; original global index 8811.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 719dd5106a2d7e170809bca9ef8f629699b008e824946c3fd5044a6660d1a38c; original global index 8818.
def localCycle00128 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, -1, -1, 0, 3, -1, -1, -1, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 2 1, .gapLower 0 0]

-- Original cycle 74c639c08299801910b8aa0a75922925c7621d62749687470c10e308b488fcf7; original global index 9046.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7598a5c6c4ae756282d9a94077f0054c5d291769252af021b20ff3587ee16aa8; original global index 9114.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 0]

-- Original cycle 75b7b3699819a48faa0cb91c89e606faba465f06b02cba3c906ff6b42ed99477; original global index 9126.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 76313ab807a157169a62bc59d3ad9da6219656494a9d8e7d7959bcbea02abe01; original global index 9149.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle 777f12539ad1fd78acecacf6d86904b6319ef0d5854af65ab63bd956ba4971f7; original global index 9246.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 77aabe45f606917054822de24f26101b1b529f86e90e62c78b35310e28827ff7; original global index 9257.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 77dc09383c44ed4708ea85bf22fbd8775294957428476964d7a6070700743499; original global index 9268.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7826c0164a75d3b36f2af242bc479ec57f84eb994eaf05225a38382cfced923e; original global index 9286.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 78a4ec3ff3a9679e6a14c7bd78f40c4497d13f362502da94e9e3e21eeb72da6b; original global index 9331.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 7928a56c4567a5baac9c97ef7a01dbb513593b334c30d4eb1f64a4c64322c8b0; original global index 9377.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 799a31760dcc7bf3232d87e909f3203c4fdd25a538b3edc693f720f5d2d29019; original global index 9406.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 79ff60e56bd4f119991a509da803ee1e7bf6296de891846b65204e749c2831c5; original global index 9435.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 7aaf8549a9de44606bae489c804e17a2ad4a66bdf9dcc4b5828bdad5b85d34c4; original global index 9497.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 7aef5ae753a309fa10c960e4265a640cf742086e574ac85f7871b001d0911dc9; original global index 9518.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 7b0ba59653c6ff7536ebec0ca9d38a8ec906ee4e6d0ba3a1621e0660fb107a17; original global index 9529.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7c29a7ee0e4c52ebde24fcbd432d19ec2494a46ab60075556bcfd65d42798ef4; original global index 9607.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 7d1094ae72642d804f77af8f151e851058c5260791e3c8e385600ee076901363; original global index 9684.
def localCycle00145 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -2, 3, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 7d123b4d584162c9b80f77c4ba726b5c2912f1f1b33bc32edb8f37cac0b9c4ac; original global index 9686.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 4, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 7df2c0229aac2bb757f95457bc98782c8c2062b7ce3207f5f5f78b555146a31b; original global index 9781.
def localCycle00147 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle 7ebcfd06948a153777e01aa76575669372b529a40a8e436aa6b63c581c5bc945; original global index 9842.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 7f733e753de56be363e98274258c5215699218f216936904880b8161cd3147db; original global index 9885.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 80345e00d09bd02a28eded3359fbecff085b40aa21db5f10499675e306316415; original global index 9946.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 836b44da4374e0b39c89faff930ca6d0c19187c32a6c45cf19e6540cea99fd6e; original global index 10194.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 837605a2d91e06c2694152aa3c6dc4dd2ade500bf12ba8d8b4e21b84c6b6f88d; original global index 10200.
def localCycle00152 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8388d9df7a666804c8e0382115f73ba9dbe985a279c440fd53125aa2fe2ae3d4; original global index 10206.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 23 1, .triangle 29 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 83f9d2d65a308cef503f222c9be63f87e9ac37db8c365bfd821ff3fad5b9e132; original global index 10244.
def localCycle00154 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .triangle 14 1, .gapLower 0 2]

-- Original cycle 857ab608bfa037ef868f9dc0d38c2511f16a8e373b0c4cdf540e2f3ed90b2fde; original global index 10355.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 860211573a50d8799e99f36623cff83904aeee5d80e7e363ba22c8ac8b5bf1b2; original global index 10395.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 865083d8dd64db9538fd926671f516dcb7e773c943f498d72c236067cbba1058; original global index 10413.
def localCycle00157 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 14 1, .gapUpper 5 3]

-- Original cycle 8804d013d37193c98a90ba9c0ffe6a3bb04c9d3e89e03ff4cd056c6653d99dce; original global index 10546.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 893c1411a379f442cd87515d5038b25f6a0b57f1935c57be5be394867a0e23aa; original global index 10618.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 894b390b30fd9b6ead426616b5b9cbe5ecddea0998ef1eb30e96d8b5d31e8245; original global index 10625.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 89b059826cf1bef92ad9bd8114a149c630d0ed88aa7e6da2e1ef81c0bcc91c89; original global index 10667.
def localCycle00161 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle 89ea9b391040c5e79e276874fd9a4f8a6fb83f72f1782dc88bb1eb519cad4dce; original global index 10687.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8b3b494f5d286982151d69ec76b3c2ccc128598e0b1e490a3260da278e6e9cd3; original global index 10786.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 8b41b5173eacc0a3693415123b4bf2d0b176ded7fd9c997a0ef34b8b50257e98; original global index 10792.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8b4cb0c06de9b919606a7f6e8d4dfdd8ad96aaea8d8c1e20b993929d03cac8db; original global index 10796.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 8bbe8df65c85f4bc5f7327ece8f61b0b89a74e5613cfdb2b8624fd3fde520d41; original global index 10820.
def localCycle00167 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 24 1]

-- Original cycle 8e65f0b36cff27592785d7578ac0f77872726b3f67acbafd87f8b6d8fb45437b; original global index 11024.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 8fb493f85c35829cf07aef94c1dfbe8af11e65a4bb496bd4d392022e5706df92; original global index 11122.
def localCycle00169 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 23 1, .triangle 13 0, .gapLower 0 1]

-- Original cycle 903d9e846ab552e45603990dcc29092e5557a30fe5d166f9758b86dd25bbbd60; original global index 11167.
def localCycle00170 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 90f765b55745510ae57059c3f6fe601215f180de4bb65f3aa21d9b6a1c2dbf33; original global index 11224.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 912bce598e8287c27671c875a8d9af363ec54770052bd1b3e43b345f3a2010c3; original global index 11242.
def localCycle00172 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 3, .triangle 14 2, .gapLower 0 3]

-- Original cycle 913d12ab83a7fe50aae6a3eab9a657ec8ca2baf5779e40c211df5f2ef037d274; original global index 11250.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 91dd22202888d44ccf411fb064688b0867e13f886313b00ce82f922fead9f210; original global index 11303.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .gapLower 3 4, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 91de8da944e9e1c01ec7a99125f85acc188b82a030a3e69d32ae70ec42a612fd; original global index 11305.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 928a672a66a4cea977a2fcd38fe221d5bed65e70253946dc5053b7a98debb241; original global index 11353.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 92f90bd3ae9c32cdb4f05996c9aaa9f7a94dc5d939dae49fe460b54a81599fab; original global index 11392.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00178 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 93e30dfbd044b10f6ef7d451f09617b50aa5224c6849adbbbcf46f4cad4b2717; original global index 11474.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 946f980ff79a407d60e0d44b277522275af3f176c69f7f2670f35daf36ea90da; original global index 11519.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 94ebdff8f787746e1edb57ee6344dca60835f1cfc0416fce7a84b7335482a3f7; original global index 11558.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00182 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 96b663a8ce0a7f6be11fae209eae36c6638c40754ce15710d3d8f9de24c8220b; original global index 11718.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 97f71d032ac15fc06ed977805144a8e375e55d90a6d116d719c326bdf76137bc; original global index 11802.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .gapLower 0 4, .triangle 14 1, .triangle 12 1, .triangle 2 1, .corridorLower 0 1]

-- Original cycle 9800abeed8e564dcecf4977d6e428d3367fc0552d58bf82072589beed8fc8c2b; original global index 11807.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 99a40325d14d209e35fa5220c053cf7cc75d7377faac40f768b6ee2ba8e9daf5; original global index 11930.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 9b2b04345cf87f92944aee458de08a41219b6480fa8798365f286685c5f58e5c; original global index 12064.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 9bc6931bfa1a54f0c2e8f63d864fe2e0d9fedfa00e03062403d1c8012c7d4f64; original global index 12122.
def localCycle00188 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle 9c6c41d295928debdbe8bd90ad67b6ae951d4c34a834f7756705271895bc71ee; original global index 12166.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 11 2, .gapLower 0 3, .gapLower 5 2, .corridorLower 2 5]

-- Original cycle 9d188c78a705f09184bd05da3ce5383e835273616fdf883b9802ea67f7866eab; original global index 12219.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle 9e33e1699e0e4ab3d2bf5560fb74157c42e47b7911a9d809be0a2cb207804e19; original global index 12315.
def localCycle00191 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 6, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, 0, -2, -2, 3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 2, .gapLower 6 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle 9fe55fe38fb18e7d3ce5e6a526a79086fa6ab7ae7f6e004f05dc2d8bcddaba45; original global index 12446.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 13 0, .gapLower 6 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a069b1ef925f8c63b803752dbc7518fb81d80f95d00e15aac0cf9080b695d3fe; original global index 12485.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle a0c472320d12fe0427ce177cc6021b339bb566efc6763b7c048147061384ad5b; original global index 12507.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a0e8935e84af7e3b4e50a4646d164f29f2c1a6ec710ed3946607dc123e284a1f; original global index 12516.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a5088963cb5b5d04d005847ee2e8090e1d105ccd3a008815324d13b8b4bcb7ac; original global index 12826.
def localCycle00196 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 6, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .gapLower 0 4, .corridorLower 0 6]

-- Original cycle a50e547f8ff1a4066e8f24d6f8b34be3e4411a2ca0d4771b105c1f88d6e20924; original global index 12828.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 14 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle a5389f0f4cf0ee495282828db1249559448c9f32c5e90b2e5364349ec2834449; original global index 12836.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle a57214e87a8c0d807fd6d32ca87c21ea30567df6fab0be2a23ab328ddef53918; original global index 12857.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle a59b40a4ff7e3ba8d45398304b990d28a681c82580568cf2bad366f140cd1f3f; original global index 12866.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle a5a147be93a7d3355c6b1fe026b09cab4bf031b3ebb06d140d99daa76ab4feea; original global index 12867.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 12 1, .gapLower 0 2, .triangle 13 1, .triangle 29 0, .corridorLower 2 4]

-- Original cycle a6996948072bef7239077ced9da1db4ae3e0206caa9ca3631895f81444273b2a; original global index 12941.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 27 1, .gapLower 6 0]

-- Original cycle a6f938f0893865ac096ca8afdc0f9e4e196d3bc94442468e5b71eeb1b828f02a; original global index 12976.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .triangle 8 1, .triangle 27 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a7f95da4608cccb2b212304880ccb43f8b2fdedf821058ee2402a09c13eaffc1; original global index 13076.
def localCycle00204 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 2, .triangle 13 1, .gapUpper 4 3]

-- Original cycle a8dc55e07156854fc1d13aa54f50bb71f19273f9cd869d0250cf17c994aec804; original global index 13144.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a910720bf2a80981c52f90a501bfec93a1bf0840f4ee75b38bd690441ee5201b; original global index 13161.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 2, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a92fcaf9ce922219e53e72acfec6a6c9fd60e2795780954e411452ade021b4f3; original global index 13172.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaLower 1]

-- Original cycle a9b33030286cdfc6f0153fbe6fe23dcada307c8cdc8fb4f4488d70023b48d47e; original global index 13210.
def localCycle00208 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle aa2ac37476bd34c41742e07a373f4021b6d82d4f2fedfbceef5c8be7cb11e777; original global index 13250.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle aa536b7c1d1cd53107e38d3a51c0001f4c5ce8b08eaf8beb97d7a7ea7e9119f8; original global index 13263.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle aa586795fcd8077757e403e803b8ba338b9bf85fc25f1d1c7de574d361ddfb7c; original global index 13265.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle aa8dda6723c3f49831a5a9ab6807a6ccef1dbea6c1d037c78dc6e3c1fbe144b7; original global index 13283.
def localCycle00212 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle aac7d7a1badc92b9066dd6a44eb76ffd197c974b5c554bcf048e3853979a21c2; original global index 13305.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 14 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle ad3295ce5160851a5af9c97382af8612dbe70ea4f10e2c1cf31ff38c64bb1e24; original global index 13501.
def localCycle00214 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 5, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![2, -1, -1, 0, 0, 3, -1, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 0, .triangle 27 0, .triangle 33 1, .gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0]

-- Original cycle aead4eda04b30301ea23e16da3432dd96aed6e43d975eee2220c18c60f76841f; original global index 13637.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 14 1, .triangle 30 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle aed67d9cc1ec3f871e91da69c74d5c8c6aa0b9eabfcc79db24dcea8b7117a3fe; original global index 13647.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b1a4fe13ce83d3f0f62c20a22a1b8606fb20eb9bb92d60869bf9d71c0091edb0; original global index 13880.
def localCycle00217 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 4, .triangle 14 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaLower 2]

-- Original cycle b1bb542e4905dc7978fb290988b521d1766766069a6a9cd98eb79a5f28f43f82; original global index 13888.
def localCycle00218 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle b1bfea308da4f5df0cea526d91b5d55b7a6ce34a0912a5dc8c6ff1b318323cb2; original global index 13889.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .gapLower 5 3, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Original cycle b23e45a37bdd86f23bb5619d4bea9ad4ff7e85587545198116e411e3e4bcf85e; original global index 13930.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b43f57a162fc441e54d0c0bd9578212c5dba16225bff0f37fab4b944ab907443; original global index 14079.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b4871cab4bdbe142b4b655bdb836312c10e95a2068959821ab61e9203a6311dc; original global index 14098.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle b553f7f37cf4b5b2689c926bb293ff1ded6be23f8171183d75bf81dcba0476b9; original global index 14166.
def localCycle00223 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle b5c9dbae4bce5e0e6f087407ae01a73543d89f9b98df1ea708f4a3ace14abf78; original global index 14201.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b5de99eb69a40e4c78e576b7720e643992fa32e403ae96b48e5d034757c7b987; original global index 14212.
def localCycle00225 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle b6622ec1664d7ec07d7a004da8668e154cb670098b3041403c354b224183ec89; original global index 14253.
def localCycle00226 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 3, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b6e9b95e00e697e344b92e0d14cce7083e1f4cd7463dc4954984efa0f6bd2f97; original global index 14288.
def localCycle00227 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle b76ebf9fb0d46428e98504b422b471dd870c8255d6fc0e9f1c582c08d92f5b0b; original global index 14317.
def localCycle00228 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle b79c9d234f78c22a2860fc585fa24357127d1d60fa1e69d3a4ffa39c24b5a84a; original global index 14325.
def localCycle00229 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle b936b8ee7379bb0668fa503b3e399ba26cb15fe15440f384b615379ff4cde48f; original global index 14453.
def localCycle00230 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .triangle 30 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b9615bdb3e9cbbc0f58bad2bd39867096cc15a6bf9dca9801cbf7d5f32d19e11; original global index 14466.
def localCycle00231 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle b981f0f2eeee68dba54380256214025f728e116cd8b473cef37d5911db8be137; original global index 14474.
def localCycle00232 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b9e122673c6fcb864e7ed99f32d81cd2b4c9517042bc0f5f728e5acc1c0292c5; original global index 14512.
def localCycle00233 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle bae8ea29ff1816ffd1e1ce9a1c25bf692fe6ab40c5e237489ddfa5e9ed2df981; original global index 14598.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle bb0b2e7172f15796a21362b0d8f5624b7c6a8a2825d96a46e07d85abfa8c93e9; original global index 14607.
def localCycle00235 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 2, .gapUpper 3 3]

-- Original cycle bb1ec48ee8e3ddb0e5214a0ad49a6f677590e4bd62c856e98dd4b471dce3d2dc; original global index 14611.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle bb894b471269ea11562357a09b849156f76d472f46f2c70f66d153049ec3a3ad; original global index 14637.
def localCycle00237 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle bfbdb0e2b2b4e0715f9ba9821bd2e5d5c073574f282e5dcda15af0f82597e710; original global index 14961.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c01fbfbff12073e75d9c4c93f5936f856f0a4fa5510319d9155268445bfee066; original global index 14996.
def localCycle00239 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c06396193593f8957ee78580a25fa7cc711f71452351561cd82c6f023e1be072; original global index 15018.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00241 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c4a98887461ce2df41589d75adfc957175ebe6be890eac749dbbfa084602b30d; original global index 15336.
def localCycle00242 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle c6402dd9dc8d5f908fbee90c1d0cb9a64531e77395d0b0cb0a2d2b673399bb9a; original global index 15460.
def localCycle00243 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 2, .triangle 6 1, .corridorLower 2 4]

-- Original cycle c6c39196f7ec3adbe0d107b02fa4461b94bcc2ff47dbb6a02f09554fc3b74595; original global index 15511.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle c7aab7dc8746f9085cc3f78cf3df071b702febad8d874eaa8667a91949c26159; original global index 15583.
def localCycle00245 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle c7fd052a0d2af7f772ba0d66305d5c39e25f7e50bc95a785f40cf7b7a524ceea; original global index 15615.
def localCycle00246 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle c841e3fc0f4b5c2792085232f0cb0098d56395b40e0d4f23bace72c41881eb1c; original global index 15628.
def localCycle00247 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle c8feaf8cadaa79f76c289e81ef209eb7057609555b577c46f6b07759990e82e5; original global index 15698.
def localCycle00248 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .triangle 27 1, .gapLower 6 0]

-- Original cycle ca3c7bd2664d0de7e439c6374449d3f9e3d0f7ba15a6ef1c182a97da8e632f47; original global index 15807.
def localCycle00249 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -3, 3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle cb6ea882feb0073130bd8458c28cf5dbd2db6076415ad62199b50a6298246e5a; original global index 15894.
def localCycle00250 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle cbcb7a82c076b7c1e783bd3ec7f51d4916850547674b91038cdcf21f5b7c12de; original global index 15924.
def localCycle00251 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 4, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle cbf484fc3d699a14ffa92cf4b1f8b9fff4fc22c913b67d51bf1697d0384a802a; original global index 15935.
def localCycle00252 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 24 0, .triangle 22 1, .triangle 28 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle cbfa0ef4cd2b8e62d9cc4a2e6fbead6432a76fe291f5d62bab81178d188f4f01; original global index 15938.
def localCycle00253 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle cd3cbb30deeea3027157032e30cacdaffeaf006208e14e62cbe6fe7e9edba622; original global index 16042.
def localCycle00254 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .gapLower 0 4, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle cdfda830cda984cbabb49fa48c03544c125e4f3a20ae03bc56fb7380f564315d; original global index 16091.
def localCycle00255 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 1]

-- Original cycle cf25ab6b2f1102aabdd7d7950ec63e470e44d6216d60212d2294fa85644a54af; original global index 16163.
def localCycle00256 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 5 1, .triangle 27 0, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle d06605d6c1cae5375da5fb3eb2d16fb20824f28f54b614b377e6d41001cd7a67; original global index 16266.
def localCycle00257 : Cycle where
  length := 14
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 4, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle d09c3204c7a9039995a718f6bcd601ad2a116c654bab8e14448baa168122173f; original global index 16280.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d40d6518aa9262f218ff6eaab396d11fc50b9e667a0264424b01aae4792bd114; original global index 16549.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle d48ebcfd48e62c59125eec377cccf4beb28d04b44e533a223ab9ddc052cc4ecb; original global index 16584.
def localCycle00260 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d4ee9de74fdf2160721c207fbed163245652bf670b1a17a8e51b97f1cc4b0122; original global index 16613.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d93fd1a4acabc1189dd4df87f129a81a8bec39ba7239c6e5a821e9d92c7bb39c; original global index 16974.
def localCycle00262 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle d94c2eedcadb5a85d282a787a30b81fff0e47fe6e1135e1dfc9b06d4bde5eb6f; original global index 16978.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle d9664c1b0bc002737cf30bb2c681558cd95e3f3257825d0e173239889431cb52; original global index 16991.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 14 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle d9c91ed7db06e310ec9971bb57e0ea092619134bb12a1bb77a799c99ad3ed002; original global index 17015.
def localCycle00265 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 3, .triangle 12 1, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle da4d127e498acf718049b9b3e4a703da1b820d773e6fa8eb271c0eec71b0e861; original global index 17054.
def localCycle00266 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.triangle 13 0, .triangle 34 1, .gapUpper 5 3, .gapLower 0 3]

-- Original cycle db22f179563ffbc668cb42ca81b41cc4a69a742bbadcf2bd8d36887dd0bdc7b7; original global index 17127.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle db33b2d2a6f2ffb4640ae4e61696fe36655fa4af02882a3b533f409dbcab4324; original global index 17132.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle dbf6cc6b626c7d7a8594184681204cb7c526cd640de5c66221f7599f70e81c7d; original global index 17193.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 12 1, .triangle 13 2, .gapLower 0 1, .corridorLower 0 1]

-- Original cycle dda2b701aab846125cbb90b891697fa9d049f0948beb763ce89063d32d8d575d; original global index 17324.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle ddb68e01af1f0628fc63d6c0ccbca6e196e89b7788a4718f50f4cad7daba9e75; original global index 17331.
def localCycle00271 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle de6e228d9117aebbf6c31bb0c7a3e33d26da898edc089ad7998d5368f575a4b3; original global index 17387.
def localCycle00272 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 12 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle df35d4cd500b8d78f4d3cdc92887684da22dfad2ada25c05375ebfe8591ab537; original global index 17446.
def localCycle00273 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 14 1, .gapUpper 5 3]

-- Original cycle e061d385a2a7c347c951e33e90e0965076f2c3b627fd6028616fbb1f39fb1dbe; original global index 17539.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0]

-- Original cycle e06a40faab80c16fbfd2ef5e2629c344bdaadc72703b22b2c025c88469389121; original global index 17544.
def localCycle00275 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .triangle 27 1, .gapLower 6 0]

-- Original cycle e0ae0b2f76484472628d88e20f897bc3713c5a0cfc67c77cc8d120c5574b7ff8; original global index 17568.
def localCycle00276 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Original cycle e2c52440cfcef00a04c51cb8555746c116455e459e58eb33ac60e36d3e95f661; original global index 17735.
def localCycle00277 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 30 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e3b099cb9d2f54c7ce3a0bf4b611a1c2100d817d86e72686b687602999b7959e; original global index 17804.
def localCycle00278 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle e4d490282bdfcce218bfc7ea9d9a255f2d09ee685eeb76de6144f8b9c306ea5c; original global index 17887.
def localCycle00279 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle e4ef5978ac14ba605bdf7bd2295863db34cecdbf0956cba28bcd2c061637b52a; original global index 17899.
def localCycle00280 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e5e78ff8fd45fb3ee5370d7213e91ca97b600d2346decb89702e0b61cd1939c0; original global index 17987.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e65c9758e8e3e21d2de04f11f59599808bef0b124e98459af640b1f8f7f90849; original global index 18025.
def localCycle00282 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -2, 2, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Original cycle e72f2b94a8400cc68dfe317c016b9b4925663cd658061c94e7bcb0416d08e533; original global index 18083.
def localCycle00283 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 3, .gapUpper 4 4]

-- Original cycle e7332bb5dd3a0c335fd65220f1d049aceeb2fc40b5a1ad8988de09dc2d2c1d56; original global index 18085.
def localCycle00284 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -3, 3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e74630e2998b3e904b4e831232d1a44c0e55ff363883d871e512a4c8144d2224; original global index 18091.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e8de3a8f4a6f8dc2a18462c25a3aeeee2c8af82956b98d9c2ffa2071e5132581; original global index 18200.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 10 2, .triangle 14 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle e9392235308234854f294a722c5e1ee2ca79a34205d3fd1d1bbdf975c78bf749; original global index 18224.
def localCycle00287 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 3, .triangle 13 2, .gapLower 0 3, .gapLower 0 2]

-- Original cycle e97f9c151d0d921e07f867edb85fea6c93a799a44c540a705db4afa9af3b9549; original global index 18248.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ea6ba3bf531fba66f13edead0066ec07809fff26306a6a5e427f369d8bd100ce; original global index 18309.
def localCycle00289 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 33 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle eae68a445be1db1284b99cb9a3e4b07d7ed80a89de4c1ded949ec3149ff4e2ff; original global index 18348.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .distance 3 5, .theta 5]
    constant := ![3, -1, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 13 1, .triangle 34 1, .triangle 33 0, .gapLower 5 0]

-- Original cycle eb40a322121665da31ce8155f2b7234fcf3096fc58626ed1452171b563a10ba4; original global index 18367.
def localCycle00291 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle ec105a3befe47335b4d75eacd97b18fe422a0f3bf40ca87db57bf38433dd8d64; original global index 18425.
def localCycle00292 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle ec1291fba90f6bc4e23a61f9a98a6adf6df28c7a390bef1a0120fde50771449b; original global index 18427.
def localCycle00293 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ec15304c3cd29136c9a120661b5940d47e39bf60902e360120b15439d9332eeb; original global index 18429.
def localCycle00294 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle ec63a2d42518d8669ba956dfb27a90256595b1c3db049def35cddae175d79823; original global index 18450.
def localCycle00295 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle ec96d8fe3b4903e9457f7429fed9c7e9c7fa73ec69164854377fe95555963c15; original global index 18472.
def localCycle00296 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 4, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .triangle 27 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ed07e66925bc58dcce1f5f72b668fa81367b9632bc193cbaa69cb7b1e96a3764; original global index 18504.
def localCycle00297 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle f0799c6149cf96913ae9ccfb22ba7489e891711c0db1b2179d61bcf72d9e9615; original global index 18752.
def localCycle00298 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .gapLower 6 4, .triangle 13 1, .triangle 29 2, .triangle 27 1, .gapLower 6 0]

-- Original cycle f2c273581bdc6242078296880b9296aa97f5897ae278a8e56b382a3e36cc8152; original global index 18922.
def localCycle00299 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f4fe9ca92cf30da76d8bfad03c54a313faca9580c439b115c63f83b3a80c9d48; original global index 19102.
def localCycle00300 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 4, .gapUpper 4 5]

-- Original cycle f5cc87e0317143415667654cc9c304cf36ef6d2ac3808eefa4b88f2dd9e3f61a; original global index 19177.
def localCycle00301 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .gapLower 6 0]

-- Original cycle f99458bd340cdf790e5fe4d641731b834d6c64642a9591f65624c455bc39f806; original global index 19455.
def localCycle00302 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fa4a4af811470127572d434d69f4fcc60311372b607c574cf17a751166649d91; original global index 19523.
def localCycle00303 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle fa5beec1a362b898cb28f6a2306a1ee9a941c2742fd0d9112692305be6a3ad12; original global index 19528.
def localCycle00304 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 6, .distance 0 5, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 2, .gapLower 0 3, .gapLower 5 2, .triangle 26 1, .gapLower 5 0]

-- Original cycle fa79ffdfe697efdb1ba36145706a0fd362a19a96486027ad2d71fef2da1eb1fb; original global index 19539.
def localCycle00305 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle fb502de53833accf490ceacc18248e59c0824f8606399b066b0db9af954b6d6a; original global index 19613.
def localCycle00306 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle fbf3089e980cbc4b024aa1c07111ea9233d29c40e5cbf7a3f3047bc9521ca4fb; original global index 19669.
def localCycle00307 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .corridorLower 5 6]

-- Original cycle fbfe2f244af7d302b0b317ca7df5cfa2cedb91a91df010af445400e2610dcd47; original global index 19674.
def localCycle00308 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc13bfc353811fb20032440ce9ee8a3f45b2e28a193a8ecd06893890e5b300ea; original global index 19682.
def localCycle00309 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .zero]
    constant := ![0, 1, -2, 0]
    coefficient := ![1, 1, -1, 0]
    strict := ![false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaLower 5]

-- Original cycle fd1b7d8309111ae67f0178cec0dcdbb3871e212b06057d1e48a7a1caffaaaf56; original global index 19776.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle fdb940b2bf4cbde4485861f54d939b754d48aed98571084454921b62363b56c7; original global index 19830.
def localCycle00311 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

def library : Library := fun id => if id < 156 then (if id < 78 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))) else (if id < 117 then (if id < 97 then (if id < 87 then (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 92 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))) else (if id < 107 then (if id < 102 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))))) else (if id < 136 then (if id < 126 then (if id < 121 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))) else (if id < 131 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)))))) else (if id < 146 then (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))) else (if id < 151 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))))))))) else (if id < 234 then (if id < 195 then (if id < 175 then (if id < 165 then (if id < 160 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))) else (if id < 170 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)))))) else (if id < 185 then (if id < 180 then (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))) else (if id < 190 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))))) else (if id < 214 then (if id < 204 then (if id < 199 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none))))) else (if id < 209 then (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)))) else (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)))))) else (if id < 224 then (if id < 219 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))))) else (if id < 229 then (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)))))))) else (if id < 273 then (if id < 253 then (if id < 243 then (if id < 238 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))) else (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))))) else (if id < 248 then (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)))) else (if id < 250 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)))))) else (if id < 263 then (if id < 258 then (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)))) else (if id < 260 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))))) else (if id < 268 then (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none)))) else (if id < 270 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none)) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none))))))) else (if id < 292 then (if id < 282 then (if id < 277 then (if id < 275 then (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none)) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none))) else (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none))))) else (if id < 287 then (if id < 284 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none)) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none)))) else (if id < 289 then (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none)))))) else (if id < 302 then (if id < 297 then (if id < 294 then (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none)))) else (if id < 299 then (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id = 298 then some localCycle00298 else none)) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id = 301 then some localCycle00301 else none))))) else (if id < 307 then (if id < 304 then (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id = 303 then some localCycle00303 else none)) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none)))) else (if id < 309 then (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 82 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6784)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 0, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 106 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6785)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6786)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 72 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6787)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6788)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 72 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6789)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 212 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6790)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 211 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6791)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 67 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6792)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 85 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6793)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 135 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6794)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 220 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6795)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 51 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6796)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![2, 3, 0, 5, 4, 1]], proof := .tail 180 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6797)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 75 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6798)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![2, 3, 0, 5, 4, 1]], proof := .tail 10 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6799)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 240 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6800)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 82 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6801)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 106 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6802)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 170 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6803)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 0, 4, 1]], proof := .tail 180 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6804)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 6, 0, 4, 1], ![2, 3, 5, 0, 4, 1]], proof := .tail 129 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6805)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 155 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6806)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 42 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6807)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 55 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6808)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 75 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6809)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 82 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6810)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 239 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6811)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 4, 0, 1]], proof := .tail 124 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6812)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 4, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 99 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6813)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 64 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6814)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 2, 6, 4, 0, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 305 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6815)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 79 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6816)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 3, 6, 0, 1], ![5, 4, 2, 6, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 127 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6817)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low6 (![291, 7, 218, 83, 138, 57, 3, 37, 248, 301, 202, 17, 243, 310, 270, 306, 119, 34, 271, 144, 70, 208, 89, 115, 208, 302, 60, 97]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6818)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .low0 (![125, 228, 176, 27, 288, 25, 87, 126, 308, 265, 86, 13, 214, 91, 126, 126, 126, 126, 66, 151, 105, 114, 12, 189, 121, 203, 184, 174]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6819)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 1, 4]], proof := .low6 (![291, 216, 141, 23, 163, 241, 56, 171, 221, 258, 120, 20, 96, 224, 183, 292, 279, 260, 209, 263, 76, 242, 293, 168, 38, 58, 146, 179]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6820)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 1, 4]], proof := .low6 (![291, 277, 32, 147, 190, 241, 56, 71, 33, 289, 230, 215, 96, 175, 227, 164, 43, 162, 303, 264, 31, 175, 35, 307, 159, 213, 217, 108]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6821)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 45 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6822)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 1, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 166 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6823)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 4, 1]], proof := .low0 (![194, 54, 154, 172, 84, 25, 87, 311, 0, 206, 103, 13, 41, 0, 80, 169, 169, 169, 287, 0, 0, 0, 12, 189, 304, 69, 196, 256]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6824)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 4, 1]], proof := .low0 (![131, 54, 65, 157, 102, 25, 253, 311, 40, 273, 200, 77, 128, 262, 169, 200, 77, 169, 136, 197, 286, 36, 219, 77, 53, 52, 254, 26]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6825)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 4, 1]], proof := .tail 45 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6826)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 6, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 299 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6827)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 4, 0, 1]], proof := .low0 (![182, 255, 204, 93, 15, 25, 274, 29, 165, 266, 233, 13, 294, 290, 266, 233, 13, 269, 266, 201, 18, 290, 9, 266, 266, 4, 81, 44]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6828)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 4, 0, 1]], proof := .tail 45 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6829)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 152 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6830)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6831)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6832)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 139 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6833)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 1, 6], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .low6 (![249, 7, 218, 83, 225, 276, 142, 100, 248, 301, 145, 161, 282, 310, 270, 306, 161, 34, 271, 46, 161, 137, 89, 161, 137, 167, 295, 161]) }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6834)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .low6 (![291, 1, 250, 110, 300, 178, 309, 117, 296, 5, 122, 275, 252, 224, 116, 8, 140, 94, 107, 236, 231, 198, 205, 245, 158, 234, 16, 153]) }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6835)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 5, 6, 1], ![3, 2, 0, 4, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 75 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6836)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 4, 1], ![3, 2, 0, 5, 4, 1]], proof := .tail 186 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6837)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 0, 4, 1]], proof := .tail 186 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6838)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 0, 4, 1]], proof := .tail 95 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6839)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 0, 6, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 166 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6840)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 4, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 99 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6841)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 130 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6842)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 99 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6843)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 4, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6844)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 112 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6845)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 0, 5, 1], ![6, 3, 2, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 261 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6846)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 1, 6], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .low6 (![284, 7, 218, 6, 225, 276, 2, 191, 248, 118, 90, 161, 223, 310, 270, 306, 161, 34, 271, 46, 161, 21, 272, 161, 118, 167, 259, 161]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6847)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 135 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6848)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 0, 6, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 240 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6849)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .low6 (![291, 49, 246, 188, 156, 178, 50, 22, 192, 111, 298, 47, 73, 123, 283, 267, 222, 232, 193, 48, 109, 123, 195, 30, 104, 177, 207, 61]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6850)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 68 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6851)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 5, 6, 0, 1], ![3, 2, 4, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 134 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6852)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 2, 6, 4, 0, 1], ![3, 2, 5, 4, 0, 1]], proof := .tail 173 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6853)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 2, 4, 0, 1]], proof := .tail 149 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6854)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 166 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6855)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![3, 6, 2, 4, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 280 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6856)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 280 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6857)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 5, 0, 1], ![6, 3, 2, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 11 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6858)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 74 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6859)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 210 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6860)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 0, 6, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 82 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6861)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 42 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6862)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 82 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6863)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 79 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6864)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 59 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6865)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 68 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6866)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 134 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6867)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 98 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6868)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 235 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6869)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 238 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6870)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 92 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6871)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 297 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6872)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 133 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6873)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 281 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6874)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 28 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6875)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 281 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6876)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 237 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6877)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 244 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6878)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 244 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6879)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 244 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6880)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 4, 6, 2, 0, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 181 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6881)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 150 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6882)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 150 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6883)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 150 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6884)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![5, 6, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 24 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6885)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![5, 6, 3, 2, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 199 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6886)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 3, 0, 1], ![6, 5, 4, 2, 0, 1], ![6, 5, 3, 2, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 148 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6887)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 187 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6888)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 278 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6889)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 62 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6890)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 62 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6891)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 1, 0]], proof := .tail 19 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6892)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 62 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6893)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 251 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6894)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 185 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6895)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 39 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6896)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 185 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6897)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 63 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6898)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 143 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6899)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 247 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6900)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 14 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6901)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 88 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6902)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 1, 2, 5, 3, 4], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 113 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6903)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 1, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 229 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6904)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 268 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6905)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 226 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6906)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 257 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6907)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 101 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6908)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 78 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6909)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 1, 2, 3, 5, 4], ![6, 0, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 285 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6910)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 1, 2, 3, 4, 5], ![6, 0, 2, 5, 3, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6911)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6784 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6784 ≤ id.val) (hhigh : id.val < 6912) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6784)) = true := by
  let j : Fin 128 := ⟨id.val - 6784, by omega⟩
  have hsum : 6784 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6784 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard053
