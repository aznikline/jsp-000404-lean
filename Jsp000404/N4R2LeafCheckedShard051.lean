import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard051
open N4R2RowDataReplay

-- Original cycle 003b2a847a1d270489eca46c2dd8a9e1fe6a4a08d623d850fe06fb16d037fbe1; original global index 21.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 0140a532fa8edc3d7b81b7a3968dd2c1bcc4ed3146597b65b50b17aa26149285; original global index 108.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 01516a812e41d1818ed1cafae8ed82d9e696971779b097096572f0f8771d8d96; original global index 112.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 01c9d59c968d3d439215bde32aff36cd06e244f04019c2ab32346c2b5e782880; original global index 143.
def localCycle00003 : Cycle where
  length := 16
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, 0, -1, 0, -1, 3, -1, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 0207346ddf14a07e407cbe2ccb6f7a03456775b897c478cfd8f68ae471db1098; original global index 165.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 02783c841926e94c5c4efb3e507016462f5d4db2c58cda07128c8da9b2f768ec; original global index 193.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 03458773f770bd7ddcba6676d6e503e39fe4dd140b3aa9236e4176e7cf68f6b9; original global index 262.
def localCycle00006 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 03954a39e580d2db039dc779ce26ab69c5e26e3d57a915c55dd42e1dfd82f6f1; original global index 289.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 055f6f8c7215b28f8a3f0b55b5824e78946e82bda3fafe4c47faf4037c9a223d; original global index 435.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .gapLower 0 4, .triangle 11 1, .triangle 27 2, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 05f25becb20822bc4aadd8b17606b2774e8836ebed5036cbf4e39e9a0da31652; original global index 494.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle 06cfa768b920603b8a344acdee83e8604010d6fca296acf250f5526e8e1a5a51; original global index 562.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 089c389ee225b548b69babda5db2e1d941d87cd9b01ca15b81430439ce28e811; original global index 687.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 0a0562719c7f680058435f9d0d8e7778540a672d66159519fe2a4e168c64f1fc; original global index 806.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .triangle 29 1, .gapLower 6 0]

-- Original cycle 0ceee17b63aaa90257f690f1de553e85dc00e7aacc26995d67d0768899393f1c; original global index 1019.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0d103fe10f4ce9ca137cd34eb5b9873981e0c8f9dcc8e88d014295e74d382c37; original global index 1035.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0d9f7d71d82407136ed2587616cb8fd6857c91b54a64a90517beeb348bc542b5; original global index 1079.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0db7ba2bba488b28787787e551ac79ddf4cc3e3c28c4c645d44f5c45d63ac6fe; original global index 1086.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 0e9b570927941add29e8373aaa30d562e0b37db815bb3e339cc4ad6a6cdd79dd; original global index 1153.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 10797d28c084fd767a3367d39620d4188264fa56eeec4f5ba137d1f0a0de4403; original global index 1320.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 11653f30c2baf76ad1104082aadcfc56f1babf4450cfa25fb7bfb259ed8d7cc5; original global index 1386.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 12e0a096a21c316505b99b81d62737c74ea43a6d04ca1c9c8bd6b6339311ccb3; original global index 1486.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 131f2985c89d090fbce3a276628dd346b328933668978127cba1c2ebb0f3d33b; original global index 1512.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 13429998cb4b52e5a20d632c4396db54fd0949100a1d1a3e664b7dcce9191a52; original global index 1521.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 8 2, .triangle 14 1, .triangle 10 1, .gapLower 0 2, .triangle 2 1, .corridorLower 0 1]

-- Original cycle 13c7f357544c6d8e9ba36de0c86ff338d4951a39c9117f30215c2d2ed9f78fc0; original global index 1569.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 14bc497eff1729289a3cabdcccbcb3a4398097195d812f69b6439ee5770ed1d6; original global index 1643.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 14c7f42756d32b5657478c46e6454913e7827f17666700b32291d7024354dc2e; original global index 1648.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 11 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 1566851a4dc20501b207b520146b974b984de010d1d1539b8990f9599562dcdb; original global index 1692.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 18f15de0d6ceb3d032cd723b074e2f521dd84fe3fa35605c29390d8b5b5164b8; original global index 1948.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 197fbcc9c5d3578d1574ffd82d74762ef1b62568fdfec772ff48070084b36269; original global index 1990.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 19ec98153b13bcc386ce3354de4c5387684501614e847a7ff9cc2e5233dd4461; original global index 2024.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 1a99d4b966fdff1e815556a43b763ef3372fb9ce6fe251b6803c00b4deb4a428; original global index 2069.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 1b5b29d1f3094e6167123d5c4e1d62018259b015fdb183a2eb39829ec2d0637e; original global index 2118.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 1c4d76da59c51c01dbbc60715f7e11f2a8b9b489f4bd39723870d56d6f916f8d; original global index 2176.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 1c8d14dd55fa20391ebe136531559deddb4d674fa5dbd807ce27b075d08cdb70; original global index 2196.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .corridorLower 2 5]

-- Original cycle 1d247bb248dc0326caf5b03bb15c59f34a5e40cf811d7133543d998fd9cc7827; original global index 2246.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![2, 2, 0, -1, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, true] }
  origin := ![.gapUpper 1 1, .gapUpper 5 5, .triangle 34 2, .triangle 23 0, .triangle 2 2, .gapLower 0 2, .triangle 3 1]

-- Original cycle 1d2ae9b03ab5ba022f988bb4668d7277a364d9b5420b00572903e0db2111d8a9; original global index 2250.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 1de55aa9c3a835414ddbcc32fe1c61ddcf1507fc1629d1b7995ce588dfbed1e6; original global index 2297.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 1e727ddbc932c473e94385c2d57383e53fee2b2e452cf91ddfc42ddf134d0af7; original global index 2337.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 1fab7f7b6232c2cf59d78b83d6e1418b3915620735b8d51f40ca3cf349ac192b; original global index 2437.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 243a1d432f1c3f88b4aa0f25086fbef5ebedcef62e48fdd36f5adfeeef794d16; original global index 2778.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 25512b7d655d3d078c405dba0c63b578338f8e2e4c732f895a798440bf680d13; original global index 2868.
def localCycle00040 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 8 1, .gapUpper 2 4]

-- Original cycle 263bf615e6dd048cafc7234dde2e9fdc53054916bf6d8bec32c2fd8c2e495899; original global index 2935.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 29451940ab5a8930e620a63e8dd7272b8118c1933a7529464e8bbf95d64dd830; original global index 3152.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaNext 2]

-- Original cycle 297b4b986400236c0b348e8790f60316adf10771dbb786404df0b20a59abce83; original global index 3162.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 29a9d9132bec99606111fe730c0badd1c79d51c779c5c7da452adc4edd99d111; original global index 3180.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2a0ef0cf43ed988926b74a0b2735f9fa9e3a6bd2f21c2cc17bfe3650190c24da; original global index 3207.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 0 4, .gapLower 5 3, .triangle 26 2, .gapUpper 2 4]

-- Original cycle 2a1f7a68539d45bb4acc843ce134907ec0005702aad6609db30d69799363215f; original global index 3211.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 2a6021c2884720d4d10784e8cfe60a36862186f49863ed36cba9bd1790b3a08c; original global index 3231.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 2b198c70776f77062c572b66fe072498b0be6564beee9850362a7a2ba8d59981; original global index 3293.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 3 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 2bc6e7f9d1cd722ea50b1e3964a5e36e33e82640612f8744be5776d198b9e464; original global index 3345.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 2 2, .gapLower 0 2, .triangle 11 1, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2cab4c2caf91998e1c9fe3711b6bbb5a2a7442d6b3952b5ed5c8af3b3ae9a570; original global index 3416.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .triangle 29 1, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 2d7884db25ea0f39c89867603db0456fe864183d54206451651905850487baeb; original global index 3467.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .gapLower 5 2, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 2e02e9533e880be826c22f6a7501cd4e20a4dcf972264d484c6fb48f90543254; original global index 3513.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2e5c942b3e05edd885334660f743149f695dcf5d3a8f9907c0d2d40b29af3321; original global index 3544.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 2ecb140be4ff8f541c05331a0d2fffc9368c29b735cb98ff8a4f2c8f5be03b53; original global index 3580.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2f035dd7f7a6fe69dd070fc82e8de3830caf4e4be10340f34939b37cbe55519c; original global index 3595.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2fdc6b8a43067fdc5aa79ac56c875ec5ebeb57ccb202d0c7c335dfb4f3bcec37; original global index 3655.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 2, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 319e2d7ae9df662b4e33eb39ff882db205452c5ac861caa06c445879ded1e3c0; original global index 3788.
def localCycle00057 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 3414eb90576984ff11aa9b321096d95cf7a643da552a5c45dfd780adbbb0244b; original global index 3992.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle 34809bbb3a71e655ae17b243751a1caa03906165cfe0ddf0f06e9fe16e880848; original global index 4019.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 35c14fa6f8d5bfac0f011374be9c82286dc9623123b0b52143a004c9272207ad; original global index 4119.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 3 3, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 382c8fe67085e3d085850bea64bbe947c60ba31ba3267a36b20256d9d1455226; original global index 4311.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 3, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 392fefe659bbb02da3b0ddcba6f731ddbbb81f9e0816808293e2b43e93aa3981; original global index 4400.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 2, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00063 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 39b0ff55dde85d935f314f9c2a64b50dfdadf35bae733eb095fb4c8496134e19; original global index 4450.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 39ec9c2022abad94129c12c1bff633ed02347c7ef76513648037cd82a087afd4; original global index 4467.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 3a6fec144ea89ca54d0a398b3ca203bef251d52e7f52e1f0d19920257448b5e6; original global index 4511.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 3bc8b0c13495a1755d103e0d2b0daf1a11e40ccc9b53694e3ffeaf6fda4bcba8; original global index 4625.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 3f189c53fc23c6ced60871f2cf589b1162b857d3991862af2f9bd088c46afe2e; original global index 4874.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 3fbb329d9859e854c2646050ba1d9c1eb52cfbbfc64e1e9c3e9e9a17fff521fd; original global index 4922.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3fc63d7ba51a08a684f92211372d150ab5028fbf9891eb1f76f306025a8f1396; original global index 4926.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4035e0f4708993e0aef5e44d32fb4a5ea62744e8eea67337203e6e1984338881; original global index 4956.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 4097ea5ef57fc87af0e464a01eaa1e928b53fc89aa8f4109435db19653713664; original global index 4993.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 40a482b67b52bc487d4d401f634d2039c0c6f48a1ebc5a93422bd127fb4954c8; original global index 4996.
def localCycle00074 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4131336c479a5c4c0510e7ff4429734e18d86dd1f18933b1b2164014550b5b96; original global index 5031.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 6 1, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 42f70301323478230d68a4b214d9ac58316c5547e1bff0d82e5d50c1c5858c9e; original global index 5164.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4456ee5e08c14b1bc941ad5357b891bba9f08d9f740fbed321f072c74f98cbbe; original global index 5291.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 449abac86e55b7b9298d7ef12030d1db6235c531a312dce58f9744e85be72248; original global index 5312.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 454ffe4f0fdd6b12f9f63b63d8ee8d45f9e5f6cc6f62758cc48b3ebdd25ceb99; original global index 5364.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 46da35c99891ff31c69bd389bf0cb6d0ef369d25c4c5fef9cb9956f71364ea4d; original global index 5490.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 4701d1c80c54cc3779cde420c829b8e026909bfa7c3d75c921b8c89f18c1ae31; original global index 5502.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 47203ca35adb7f7e30ccd36d847d59669670a2c007eb26a267e546e995011aa5; original global index 5515.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 11 1, .triangle 27 2, .gapLower 6 0]

-- Original cycle 4a373a4c2889d846287b363f8f6f788ccce42dbafd8d13da1085dc773591f051; original global index 5754.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4aac45f5552cc717a02fadca6d794f578a0725e75be2c83f816b1340cd2daf1e; original global index 5790.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4ab60690461579897eb121a90948d93f1d780e2b3628c2e86b697ed279730372; original global index 5795.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 2, .gapLower 0 3, .gapLower 4 3, .triangle 25 0, .gapLower 3 0]

-- Original cycle 4b0681f640c91da82ff127c66129245895035cb3ca179a37f156596f606836c1; original global index 5823.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 2, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 4e1418591b13977553f31946f1cb688b74840ca7d5b7136c3bda358d42301365; original global index 6060.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4e2344273291d395437d7ef258af13e170d67b4eb48dd1dc02251d9aa230194a; original global index 6064.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 4f03db72c3abd582a765197c018aee1de4fc0a35448900d542642dcc31b65c4f; original global index 6139.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .gapLower 0 3, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 4f280ac6c43690955e7f2196a5a1e7554458745bfe9fa470afbb48fd8a373cab; original global index 6148.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00091 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 500eab0048e5f8ee5c63704180c9f514b22e3ebb639a8a8618ad5811090fe810; original global index 6215.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 513f0eb7a92de791d94a1667968b2a75cb250b32cf8684fcc8e11cd0c2574e45; original global index 6316.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 51837d4d4ea77120e9768ec24375b7842735c89d589f1b411f01260f361a989a; original global index 6343.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .triangle 10 1, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4]

-- Original cycle 51a95e03a7da554539bef775d5e1bdcf3125071341bf07cea4eca55cdfcbb4a9; original global index 6355.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 3 5, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 3, .gapUpper 3 4]

-- Original cycle 51d8c86147dd46ea676de02cb118cb400609f1692b92a46ce8b5ca79eab451f9; original global index 6367.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 52446932c711798105803143db6f7d234abc64a62d20e15cdfe2d30c8280d6cf; original global index 6396.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 543ded306c10a769dd148a5c1febacb4c17d6a36e4b72446b69fd9463a053071; original global index 6524.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 54b3924c72a6ad1116fa02e09f07f81cfa28849ea4dcea9bef1e1fdaf48ff5a9; original global index 6560.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 54bfd16e752a6c5a2ac15a92e9c6dd178eb7b7be8ea7289532ecf25d6655ec5e; original global index 6567.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .gapLower 0 4, .gapLower 5 3, .triangle 26 2, .gapUpper 2 4]

-- Original cycle 54f6b488e559d97ced043716555551670e310ac54e875188a8be4b0a885ae094; original global index 6577.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 0 3, .gapLower 3 2, .corridorLower 2 3]

-- Original cycle 552e21e2f8c44c3633073d0a8f0395115048b68e38ca122a1d3c285f8e501593; original global index 6593.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 3 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 56d1463b1af6bc07120582b6b6db50f7f2345fe6ed7a76053a0a8cc5729abe41; original global index 6728.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 56e89d2611aaad63910615cc0ace0154bb2f38a0186379bd44c28846f76e17e2; original global index 6741.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 56f4c921d1ce2adf447ea1fc15ace64fbeab70f924bec544790c78e5e19c4c11; original global index 6743.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 5721c5d34c15391d0e4fbd715cea1995549b13f505d9e687340f1c4197efddc4; original global index 6753.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 57e1f74b7b65def75426ca254e061556aa9647ab5a8e5b6c6f91ffcc7c84425d; original global index 6820.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 57f8cc4cc21032ca25f6ab1b61e2fda70881f6547dbac8ccdbbfbc5c3c717d74; original global index 6826.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 58d4e897d02cc3498b83fac7b68b2e4c14978409f918b7065e604d72ced3ec92; original global index 6891.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 592a41dd95819a9c2be68576a73b853b1c863d7b911022104cdfe70517f68dd6; original global index 6914.
def localCycle00110 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 2, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5b48edfac4febd641ec8f761882bc6d6b252689f5551f8cbb56949b012f7f6ca; original global index 7107.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 5c1d62a5fd03f555adc81bb02ce31ce454d4835b50485bb77e8e09a9c829f4fc; original global index 7171.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5ea46b492f3e4e840db4ae634ec2eebf12007418b4aad6b6fdedf50782c9d7bd; original global index 7362.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5eef746695a0dffe1c281a0f9c3f888f1071011fc884d13724ef6390b435041b; original global index 7390.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 14 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 605cb5c418ca27115996916bd14887fc1cf7f823de2bac9969237129dd50ef95; original global index 7504.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 6209021cf9172f7f93d36bf6fcf38d32969b46078af7401e583feaa52b4e5399; original global index 7654.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 27 2, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 623eabb30cb1c9b9416ccb69e4a81fad99ba1c72ace1be425eea21b4c97bb12d; original global index 7666.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, 0, -3, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 6633dc2eae4ee3ad3dd2505adeb8241621238b1094b978717ec9fdb115339158; original global index 7949.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6a780b35aa210210be6297e6e491bc1eaef13ee04b58d14d1801c3e6e98c89ed; original global index 8291.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 3 2, .triangle 14 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6cac8b7c1eccec9737e4511f17258c02489236dcd59441f7aea9ebb1315743fb; original global index 8456.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -2, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 6e082cde6ffa461c80c520106489e5569e20c7ca84c78414b80232d81f45f92d; original global index 8543.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00123 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6f3126c580b717fbcfa43657234b202b10b95407fa2eee32d249b4c762906f29; original global index 8620.
def localCycle00124 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle 70bba30de177614fd786012efffbe4f3efb3b3a66c371c055490c2615c494e0b; original global index 8738.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 70d61a3fbcfc9471b66f961686ecdc4757e12ecc49bddd75d971e7242c91485c; original global index 8744.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 0, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 70dc4c64dcd8345c12e74689eae12b91dc360652e4ad06243ee8a828625da85d; original global index 8745.
def localCycle00127 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle 7105095f2611a48316ff4eb035feac3dae07f650ffbb49f5daa777d6edc56b84; original global index 8769.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 73030681adb68de4cd18e05a784b6d2510c3114ae2e7e668090957884d1ef614; original global index 8910.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 73136d601c5d4abaf9f458444c497f9e2e3d084c25ee8ad7319431dce541707d; original global index 8913.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7536d3d71df16bc843111da1f305a143ac83519db4636fdc70b8b580198e3f72; original global index 9082.
def localCycle00131 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle 7614a058d51f0cfc12325470a0e75c513b650ae217f11082fecccb3939ac6ee5; original global index 9142.
def localCycle00132 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 2, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7696037fdec1e202c6a77d377d7119b3a596a8f86ec1f776ac8d4688f080de64; original global index 9177.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 7700c4bac468d5d97a0a17226d13450fdf1107c73b488a7c8c863b6afed60116; original global index 9211.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7924bef1247ea2dfeb1fd58c286e06ddba5fcbaabf1329cbf4baef37da595529; original global index 9376.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 24 2, .triangle 4 2, .gapLower 6 3, .triangle 27 2, .triangle 29 1, .gapLower 6 0]

-- Original cycle 79558bf2a55353d1771fdbd8c9509b2d3688435e780b3ec56ea47668c83a3836; original global index 9390.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7b01b4b0de2219d07ed1b261786d6149ac64491466fce4725549ef6f2da4f920; original global index 9524.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 7b1e5adbfd784cfedf474914a63b4bb4e5a6a99d4b1b9b639a5177fa17e3dc60; original global index 9535.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7cf406f6ff441e3075d96664c9abe72b276e1021ad514254581a058e097335b3; original global index 9675.
def localCycle00139 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7e570783ebfe3ef3cbf684c1ff64c52e614225281c7c2ba406bee9d2f534b6cb; original global index 9813.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 3 5, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .gapLower 0 4, .gapLower 5 3, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 7eb6912960bc7077b99a79073f9ef820e613a18a879cd0cb5420891451596996; original global index 9837.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 7efb8ac95fb4805ddb2345744ad2b62cf8a067ce7fdd6ad1bbcaa2b2e99324f7; original global index 9857.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7ffd9a4a76675f323f6d719a27d6871c94d88b471b53e36300fda6a24f1b307a; original global index 9929.
def localCycle00143 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 81b8e5664c93f7c6ba726a162fc10f98d8caf091b3c5e681bcfe6acc500d0b75; original global index 10071.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 81f78ca8090c4089660b0b9f444f7c4f5539a5a91481fe01b77556f1fe876811; original global index 10090.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle 83c7a6479b56e98ee1b73087d2231d1356217ec6c785908427f232f0ce3c0827; original global index 10227.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 2, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 83da27750c5ef2539493511e0fd5df49d556b940865b754ef012c2de9e0d3dc7; original global index 10234.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8468c7b6dc0e8f64c45eb98ca65c3f0526490fc4fc933738284ab706b33b6b62; original global index 10282.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 29 1, .gapLower 6 0]

-- Original cycle 85640f57d5c544a38c53a8b49eb93d0ac47a62ec5a2c15e1b087b5d163e2f20c; original global index 10349.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 2, .gapLower 0 4, .triangle 10 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8663524208f712b6c7ab273bdedeff47c4f7bd895f5eb6b8816e4e90ba4940c0; original global index 10420.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 86f3bc04e7a947a621ea4fd8b024b07b46e58f124fededda04b190586cdf1b9d; original global index 10466.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 87ab80c4c2fb6c72e950d96ebc6f0de29626e2b4cb0c266c1c32d1c7592ab53a; original global index 10517.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 88e206989a67537bd45d61ef62d4aa718c23ea5521de80ff2a4775464348b742; original global index 10603.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8a121e845bf39c396b42102b59c7f43e9b9328d547b26ebd282b7c6493c173f4; original global index 10700.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8a552c5603bef9eeae673afbeb4a86a714e6b199639893fcf8e9ea51265e3267; original global index 10719.
def localCycle00155 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 2 5, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 2, .gapLower 0 4, .gapLower 5 1, .corridorLower 2 5]

-- Original cycle 8ad01fcd9354d49d2c3e9471c9d46011285bb07f07608ba15b847b49e42d742e; original global index 10756.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8b23bd5363ba982f88295aa3b9b7905cf9efec53eeaba33f68dd36810a04a23a; original global index 10780.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 8b41b5173eacc0a3693415123b4bf2d0b176ded7fd9c997a0ef34b8b50257e98; original global index 10792.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .gapLower 0 2, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8bda48549d40d46d9bafbcf8fb02162cd3f5acc387ee6a599e839ec7fb9ecf61; original global index 10827.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 8beb3cfd53ed11d5d891ec630d7ef9ad27677ca57b2775717d593b668d019534; original global index 10833.
def localCycle00160 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8c57b88158f3083a2ef18d4f0d51bc43c9072169c9bc3f8f031ceb7fb5fad2ea; original global index 10858.
def localCycle00161 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .triangle 27 2, .gapLower 6 0]

-- Original cycle 8c93ead90cbc5ee648023255c53a84305ba586467c8bf1171552d02dd9280a39; original global index 10874.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8da864fd4ecdff17cd640b2bed946ba2a4742e5f4a24993e56a6d05d93abc822; original global index 10958.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 8ec75c7736e3e3e6607ebd5b264cb7d62b5ba82c69726131a83c2c78cf51a4d0; original global index 11050.
def localCycle00164 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 90411a7a5fa6498701260a46844d72e5133d9082118164df98ecc34fefa9f42c; original global index 11170.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 2, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 929eedb8995cf4b7d131d31aad0034737ee57cfbbe352584189d50be7b4a80fd; original global index 11359.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 92b146dbfb25d3c7f1f932cb688e1ea27d312cb264539eeac7ecf14c0c905292; original global index 11367.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 4]

-- Original cycle 932d14239ded5785003f9ae57321441e6296b28d950dd4735a4f2f9ae0a50ee8; original global index 11412.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00169 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 939cfa2e2cd97f758def0342143958cae6f6d2100376069cea34aaa083f194a4; original global index 11451.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 949f499d382636b825ea5e3b1f99adac312948189d01b5c07f77dcfc75c9c9ff; original global index 11532.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 94aa3e76d08d339dd1d0579c8dae8aae5feb0db5bcb96dee01b41e70d768b377; original global index 11535.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 953e8c21043e6a5d896c9dabb8399b4b7eeb46af07fa031725fa48c84fe02edb; original global index 11594.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle 95d28898534bb0d357d433e19ff5499eafd2007f104c2ad25e8ade7b786ed65c; original global index 11645.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 6, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .gapLower 6 0, .thetaLower 6]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00175 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 972626c704f82ae3d6edc9d5f8990fc6580df12a1f5ee89286518214ffcad93d; original global index 11748.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 987e028371c35a7826354eac73ec94a93b24d3a61dcdea7f0e4efe48dba67299; original global index 11842.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle 98814f71338dcda44b585d98a1e0cc95942dd75a202815946ddb9be68e616c46; original global index 11844.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 98b669204caf495287fc6c46b52329635fb5f7ef8255ac5d70db08dd7fc64bfd; original global index 11862.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 98c1a373d31062fb9529d825c89456b23c6fc75373243c5fea0765cc5b0f902e; original global index 11864.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 14 1, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 98d8b795d1d7c4df26f5b2b34b2dc050b61fd80785cf2e565b3127af0bddce63; original global index 11868.
def localCycle00181 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .triangle 10 1, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9afae20174345ac17cf3393d1ce6f890f304923493fce3a3313327a6859dda2c; original global index 12045.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 27 2, .gapLower 6 0]

-- Original cycle 9bbfdb114e1f991ea65d4441fe7ab6245aa9209694ca6c1dc6fe63cc6304e0a1; original global index 12118.
def localCycle00183 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 11 0, .triangle 27 2, .gapUpper 2 4]

-- Original cycle 9c11ce114ecb6dc8bcd8304d3c8ebbe0e5ed0877869b48c9fe6b49c9106047c0; original global index 12140.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 9c80c84c3c3326c3acc40e823977da357e8540e1b5c36ccf84afeca27079a132; original global index 12172.
def localCycle00185 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6]

-- Original cycle 9d5654df64d7eebb5c1251ae107af89830e6e23c26ff1bc8419535e2109e842d; original global index 12239.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .gapLower 6 2, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 9e143836cae4d94368dd3a9796942d9e029fe3a418b2ebc5eff801f71f5491a1; original global index 12302.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 8 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9ec73ab30eb16af8ed4970c04d4f27d3939d428e13ab2aacd2cfdc6dbef8f85b; original global index 12363.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle 9fbb90bd3926bc60ac50dd674cad04d76468b70969bceeea4e2d8c71fe612e96; original global index 12431.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a164dbe476cb29841c77be74f5dc76366f37b97a7eb985e0e79dd2fb30c98d94; original global index 12550.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle a1a4b6fdba4d711cd8f781b10b5ee1cfa1048c5f3ccaad0f4889c3f01ba6133e; original global index 12573.
def localCycle00191 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .gapLower 0 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle a1dfd063f0f5c2543f56a058d9c5ccd4d9c59e58a48957744d9ed6a6263069ee; original global index 12588.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 30 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a3e7ae198577e06582d1b0c42c8bab557c92ec80d317eeae85128d722da69d3c; original global index 12745.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 4]

-- Original cycle a4cce42e079e92e4d9065f479f6055e9f01ba77f4c7398672528dbfe0575d2c0; original global index 12808.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a764d99857cd2ce15ed10ce5a8026f0748a19e3d5e158d6990930b73c51f6368; original global index 13024.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle a8a90c7cce00e56ea72cdff094a6660ce05c23469902724aa0a38ec59644ff66; original global index 13124.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .gapUpper 2 4]

-- Original cycle a8de46fee15b16db1a30b54bba1887a1d38958f4e9f68cba96b474ae78332c91; original global index 13146.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a99407b040f91eae9de2adf1e16c7fef0da29b526cd10cc975fa7bc41d05d248; original global index 13202.
def localCycle00198 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -3, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ab2be0bf01656099b186eecaba07962761b9325785a1ae9803d238561d32d329; original global index 13333.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle ae69618e1a1691c535ea8403b3e9363adf2f5fabcc46b2fd3aaecbc936185c08; original global index 13611.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Original cycle b0109989341fae1a070a9ba51c173e71f555dfd2ad2ad57d939d591967b49809; original global index 13744.
def localCycle00201 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 11 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle b0955666b98b8b5a84fb76b12572a1881703718dc35a90811eb2a0cf5a4e0f1e; original global index 13787.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle b13a78212c8c72c76bf8d315c304b5a9025971c16373356cd62ced44ea289bee; original global index 13843.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b45479689e23feee5882f0cd949e17ae3928104316c843d77ce65fef57b64d6b; original global index 14086.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b4d9ac179e5c66e769dda42b7b6ec26dd394421f0e270f89ddd0dd857dfe5174; original global index 14124.
def localCycle00205 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 2 6, .distance 5 6, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 30 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle b547f9eee5662146c634ccebd2dfa5936c3abd27e761094684f9a93d432a5c61; original global index 14163.
def localCycle00206 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 0 1]

-- Original cycle b6407690fc000d96a40f3288270bde06a84db37658f0a3d7d78246a0665056c2; original global index 14239.
def localCycle00207 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .gapLower 6 0, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle b6958de1711ddef2ddaf4b4eb2b8c58436ba85615966a610176a1e5f0b8a0252; original global index 14270.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 2, .gapLower 6 3, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle b6e23104a1bfc5fda4aaf38638c951797516b2f82eee6bcc6025665b1b42e39f; original global index 14287.
def localCycle00209 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle b6ede93cd77399c7c67f6f5111447cbb9b0c1dfc9c0e573699d5dc541597c256; original global index 14290.
def localCycle00210 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle b76ebf9fb0d46428e98504b422b471dd870c8255d6fc0e9f1c582c08d92f5b0b; original global index 14317.
def localCycle00211 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 0 4, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 0 1]

-- Original cycle b7df01eab562b8d9db1ea86c3ef449ca051cdbd9d65ef4a489df9f3a7a79093e; original global index 14347.
def localCycle00212 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 2, .gapLower 0 3, .gapLower 4 3, .triangle 25 0, .gapLower 3 0]

-- Original cycle b82fffaa0ff23ede027faedd0076fd84c52ba45a0ce71c38a33199d78ca1a030; original global index 14368.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b8c9c7cd27fcb2654a8078f8a360ab11975995470bf6b5aadc4424205cd0c512; original global index 14422.
def localCycle00214 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle b8dc06bdceb25343f6fc906013f020b580f4440add8832bb5dcd504c3b183f18; original global index 14429.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .triangle 4 2, .gapLower 6 2, .triangle 27 2, .gapLower 6 0]

-- Original cycle b90dc433c5f42a5fe099088d2bd4bba78449c479399cbda7ccd3367196ece2de; original global index 14439.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 3 3, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b9e9f5cc39fb62169bb42c57c57d6f776afe4de6f82c2f4fcd0263a2f296db78; original global index 14516.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .triangle 8 1, .gapLower 6 0]

-- Original cycle bb1baf84c9f0653b47a16ad0a24fbfb480943c3414cde8b9a3115b01069e6175; original global index 14610.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle be28ff84831f9f432605ebde46e8d683284552a28a03b97b54689de2738ff01b; original global index 14830.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c19321dbb69666de97c4d31e4162c91599c6f61ad1f047e5cfb007f69a70737b; original global index 15119.
def localCycle00221 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle c23a10ff8a6b991b6bf3e45d0c804cc91527450824588d8f0d21cefc5a091da5; original global index 15165.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 2, .gapLower 0 3, .gapLower 5 2, .triangle 26 0, .corridorLower 2 3]

-- Original cycle c2b26a2f3c6f417374d26fb6253f9edd3b2c4701ea804f3a5ae406d8e7a62ee0; original global index 15197.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00224 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c4067933b87279444357be86a1945e2aa3efcbd8d5eafba15f80c3143b2819cf; original global index 15289.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 26 0, .corridorLower 2 3]

-- Original cycle c5e4f74a8006afc2966e31129ddf396b9d48c18cf8937a50b3779d0aa1cc941f; original global index 15431.
def localCycle00226 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle c6192eed567b4999e321d06c65eb7a5b766c7fa1b7f75c8e6a136e45a174e4fd; original global index 15453.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle c69c5e45a271ff2698654f0aa07c3cb3940e6aa01435691c9bd376e87495b8af; original global index 15492.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .gapLower 4 2, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c720be6b588e74aebc6d5d4e1ff85b2b107f0e846e7f7a54a8cf99fe25dd076b; original global index 15537.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .gapLower 0 3, .triangle 13 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c80b2665b2bf44f5647702f88968b131bb679d369491fe949d35626172c86b0b; original global index 15619.
def localCycle00230 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 3, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 3 3, .gapLower 0 2, .corridorLower 0 4, .thetaLower 0]

-- Original cycle c849c74de9e5bf897742ad610834523a56b8d1f4377e1ca8cdb12e2b57160ee9; original global index 15632.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle c92735819a814f834e2548ac3195a50d905b9cd9f3b3f3880001aa9d690d7c97; original global index 15718.
def localCycle00232 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 5 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle c980091e9fb1bf215474f44d663d34fed064e11d298d81bfdd5ce4f5184f9f2a; original global index 15755.
def localCycle00233 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle ca61ebf6c0d5404d9f0f4b686621aa265296901bad0e31270abf7b9cdab8ea78; original global index 15819.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cb56a8154462a0a6556944229083114cbfce9f796221722d870f655c89af86b0; original global index 15884.
def localCycle00235 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cdfda830cda984cbabb49fa48c03544c125e4f3a20ae03bc56fb7380f564315d; original global index 16091.
def localCycle00236 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 1]

-- Original cycle cf29a623ae84105f8f423a806278fa1d666e3062ee7b652343acfcda22f331f2; original global index 16167.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle cf761608f179c8198ae4746cc589739a8a2cb5da4a71681dfb1fef40b6f9458e; original global index 16188.
def localCycle00238 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cfa4321b72899c76059e4b699dbe9232c8afd85932570dd3b13c4291c9fa78ca; original global index 16203.
def localCycle00239 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 2, .gapUpper 2 4]

-- Original cycle cfbfd37f38f791265a166cfeda74d93f5f11f36ac0be45f6f5f286c9d564ba88; original global index 16213.
def localCycle00240 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d1f9a7ea6dc4672df44fb747e65cad456bf94d8105abcbc02e3ecc02d396dd65; original global index 16387.
def localCycle00241 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle d262c726ae0aaa87b528e535551505d2d4ad4a21a1530068bfb48a60d346bb50; original global index 16416.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle d26e39c1fb5c7df2506511d48eef926707c24693c166046dd12b9a8559603230; original global index 16420.
def localCycle00243 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 14 0, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d2fea683287af5b80ae7ad5f515c2b17f921e4122a076a8b4a2c8bce5344f38a; original global index 16457.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d341b34a6253a740408f953a3275cf779dffce758f7a54f65ce21514d69a656f; original global index 16479.
def localCycle00245 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d36db4e88f6f9ff1a9c684ef202dcde19dbd841e6665cd266d7bd6ee8a05f9ae; original global index 16493.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .gapLower 0 5, .triangle 14 1, .gapLower 0 3, .gapLower 3 2, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d378665e2e23b96ca14142c05389ef6caec4ef49e876e14b83f7cfca04cb5e76; original global index 16498.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d3b665fd249f507e3e2fac4628366ce4a6da943fc6d3ae50c0d8f4cbe990617e; original global index 16522.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d468fddd8a6c38bf6ad4cc4b5c169b48741babb6908a4c0683b586a66dc10965; original global index 16574.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 2, .gapLower 6 1, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d4ee9de74fdf2160721c207fbed163245652bf670b1a17a8e51b97f1cc4b0122; original global index 16613.
def localCycle00250 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d6bc42e6242ad4c7f9b5bf6b4d98d39eadbae3790d6824a73942839c0865b24c; original global index 16763.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle d8a417dd2532b26b67f7696766aed495dd8dc031f3368d94f26c88ee410dd1af; original global index 16909.
def localCycle00252 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d903649eed7d70a3c70675e7ab0bde06c49e65d282751b7be89ae9886b8c5732; original global index 16950.
def localCycle00253 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle d9288bc57f57bf4037ffa80d004697dc0c372a3d9dc4bab94ab84bf88a7ff3a4; original global index 16967.
def localCycle00254 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 10 0, .triangle 26 2, .gapUpper 2 4]

-- Original cycle d9c91ed7db06e310ec9971bb57e0ea092619134bb12a1bb77a799c99ad3ed002; original global index 17015.
def localCycle00255 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 3, .triangle 12 1, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle dbf6cc6b626c7d7a8594184681204cb7c526cd640de5c66221f7599f70e81c7d; original global index 17193.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 2, .triangle 12 1, .triangle 13 2, .gapLower 0 1, .corridorLower 0 1]

-- Original cycle dc2d88011d27248fe1a78439f37415b840eb4425a01634c48b313669bfb23745; original global index 17207.
def localCycle00257 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 0 5, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 5 4, .gapLower 0 1]

-- Original cycle dcdf4184bd5cd19b62bd16cc9723465064ac765caf4187d78ff20160dfc30ec0; original global index 17261.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dfe29c603dae67e669cd9a7132d7975dddb8147e4f221d4f5f103d697199ceaa; original global index 17496.
def localCycle00259 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e1d8c0071f4ef742204d17c90b12b880677958e90ed7198dfc3aa74827a8d441; original global index 17662.
def localCycle00260 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 11 1, .gapUpper 3 4]

-- Original cycle e24f51e4fef8a7b25b4e2453ead5bd65ac68ffe66f6f1a1512cdcd3f85505d0b; original global index 17695.
def localCycle00261 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00262 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e3f02d80c2fc00c4e392e7f31c22b526657a23e8faa37f557edc8825eec750fe; original global index 17831.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e4635f82c675a385f2fa100a1da1a0ef9d05c4b632d081f5d2af6427bbe4f2ac; original global index 17853.
def localCycle00264 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 4, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 12 1, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Original cycle e4e403a57678f908d31804ff6c3c551ee6ebc149df7410fd210cf89af0c191c7; original global index 17893.
def localCycle00265 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .triangle 27 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e54925086159362b0d5ff0d1b0ac1ccbf3bbb2560637a6437c50a540e0156752; original global index 17925.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e7beb18c30b4c659a64adc1e22eaac338b6a882268f7eb251cbc6a6a41d8fc3d; original global index 18123.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 5, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 0, .triangle 30 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle e83754ceaa3a81dd085b18d983a88b90ebf913b917b78a1cc55af93ab8c1dfd1; original global index 18153.
def localCycle00268 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 11 1, .gapUpper 3 4]

-- Original cycle e8d57eea051172dd5941e5dea3b6f4a806f7fe56a05e02c86a9baf626eaff792; original global index 18198.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle e9744a2e5a9641a5dec61b31453dc52d14c670f966be1d98af55c08734822a1a; original global index 18243.
def localCycle00270 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -3, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 5 2, .triangle 11 0, .gapLower 6 1, .gapUpper 2 4]

-- Original cycle ea0781fb605d308182422247566cac8de690a4db14c079bc9e18838501ace7a8; original global index 18282.
def localCycle00271 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle eae7652c36044ae93f6fd59bc6dc3010e99314f36d3c105dc456da8afcca5d54; original global index 18349.
def localCycle00272 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 3 4, .triangle 27 2, .gapUpper 2 4]

-- Original cycle ec1b192ba72613252192e3831aca75ca22cc53cf11da5917f9f8ae2a43f23cfd; original global index 18431.
def localCycle00273 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .triangle 8 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ec5db089771d987f6395afc3a4fc6bffe0fe84fe573c24804d88e43a7d6c75da; original global index 18449.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 4, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .gapLower 0 4, .triangle 13 1, .gapLower 0 2, .gapLower 5 3, .triangle 26 0, .corridorLower 2 3]

-- Original cycle edf908678ef676dd94409988d2afeb7734ba8593bfee380a75076dba7a0da200; original global index 18579.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f0a9824bda98e96d1af51cdb4ae5de3999ca7bcd40212e871e3f122c19ce08e6; original global index 18770.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 1, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f12bdafa686ee37211914e275844ffd7a7d8b1c9423052232faa56a75eb2c320; original global index 18811.
def localCycle00277 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 3, .distance 3 5, .distance 3 4, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .theta 0]
    constant := ![2, 0, -1, 0, 0, -1, -1, 0, 2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 5 2, .triangle 10 0, .triangle 31 1, .triangle 32 2, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapUpper 1 0, .gapLower 0 0]

-- Original cycle f19457f624464f9ab3906c8f71886fcfab5f875c09a4e310cf0168b59c7daba2; original global index 18836.
def localCycle00278 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f38036c16e033a3022e83e25e1816ec0b2361019e53c011df8a392a75d2c8f56; original global index 18995.
def localCycle00279 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle f4657372bfeadf64919563758a6ab14f2a4c4e542ab96fd8a1f1f3cdd4e0db9c; original global index 19052.
def localCycle00280 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, -1, -2, 3, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, -1, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 8 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaNext 2]

-- Original cycle f490b6ab9647f178e40c69204011daacf8e83eb61c9ffb264ed750a52c69a41a; original global index 19068.
def localCycle00281 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 6, .distance 0 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 11 2, .gapLower 0 3, .gapLower 4 3, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f52047880dbe3876901d951a097b9eb06a607cad35e36e05265624a71155da46; original global index 19109.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f5be85e7793260448894b635ed6dfaf7175448864bbc28329a86fee83295982c; original global index 19170.
def localCycle00283 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f6290c0ca9857e002c93db4275c5e0b5b8472529d95ae58e36d63e76714bcecc; original global index 19204.
def localCycle00284 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f69e2ebc8997f896c0d0841d384402ed1aca9a6190705ab692fc297e19d7a3d2; original global index 19242.
def localCycle00285 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 4, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f797862253a72699aea21834cc3920cf5ee4f80cd5709202c00b7cb04d223ed7; original global index 19307.
def localCycle00286 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 3 4, .gapLower 5 2, .gapUpper 2 4]

-- Original cycle f90c8e2597324cefa360270629c26eae5fc94b2e2907490d66ca53477fe3b054; original global index 19423.
def localCycle00287 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle fbfe2f244af7d302b0b317ca7df5cfa2cedb91a91df010af445400e2610dcd47; original global index 19674.
def localCycle00288 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .gapLower 0 2, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc795d141c2f94eca2fa6db718fe982d4ab52f9e6687f7ac76f588ff75338525; original global index 19724.
def localCycle00289 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 1]
    constant := ![2, 2, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapUpper 5 5, .triangle 34 2, .triangle 13 0, .gapLower 0 2, .gapLower 0 1]

-- Original cycle fcbbd612496dd7d4803c9c77327c48bfda7d9e7776c067e3f849054d2fd7b4b6; original global index 19750.
def localCycle00290 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fccd7b76d9dc268815b448b486d4ee4332661c5186daf257cb5b6fa8f5657147; original global index 19755.
def localCycle00291 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fd928529314c6ed46914a134ad6f3a8055cf9727023a09ff0f664dc69342fd3a; original global index 19821.
def localCycle00292 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle fd9d4ffc03eec3a82bdd82bdfbaabfc68f21ac25a000fb9e8eecc9975e0a2364; original global index 19825.
def localCycle00293 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 6, .distance 0 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 5 2, .triangle 10 0, .triangle 33 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle fe0841dbb580841b13d7374e1a14724bd5ed0b7cc7cb6fc3fe246fecfa2ca1e9; original global index 19851.
def localCycle00294 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 0 6, .distance 3 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle feb65f876a1a32d7b2e2361e68bb213181346a37d5629c8670c636ab86f9481f; original global index 19917.
def localCycle00295 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 2, .distance 0 6, .distance 0 5, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 2, .gapLower 0 4, .gapLower 5 1, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0]

def library : Library := fun id => if id < 148 then (if id < 74 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 55 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 50 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))))) else (if id < 64 then (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))))) else (if id < 111 then (if id < 92 then (if id < 83 then (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 87 then (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 101 then (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))))) else (if id < 129 then (if id < 120 then (if id < 115 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))))) else (if id < 138 then (if id < 133 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))))))) else (if id < 222 then (if id < 185 then (if id < 166 then (if id < 157 then (if id < 152 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))) else (if id < 161 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))))) else (if id < 175 then (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 180 then (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))))) else (if id < 203 then (if id < 194 then (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))))) else (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))))) else (if id < 212 then (if id < 207 then (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))))) else (if id < 217 then (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))))))) else (if id < 259 then (if id < 240 then (if id < 231 then (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))) else (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)))))) else (if id < 249 then (if id < 244 then (if id < 242 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none))))) else (if id < 254 then (if id < 251 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)))) else (if id < 256 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none))))))) else (if id < 277 then (if id < 268 then (if id < 263 then (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))) else (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none))))) else (if id < 272 then (if id < 270 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none)) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none))) else (if id < 274 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))))) else (if id < 286 then (if id < 281 then (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id = 280 then some localCycle00280 else none))) else (if id < 283 then (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none))))) else (if id < 291 then (if id < 288 then (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none)))) else (if id < 293 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 47 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6528)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 84 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6529)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 138 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6530)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 66 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6531)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 109 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6532)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 162 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6533)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 113 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6534)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 10 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6535)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 278 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6536)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 238 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6537)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 130 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6538)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 96 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6539)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 116 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6540)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 160 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6541)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 57 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6542)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 156 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6543)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .low6 (![11, 270, 124, 92, 198, 64, 134, 201, 215, 82, 182, 161, 110, 287, 201, 201, 201, 201, 163, 1, 56, 62, 240, 114, 35, 20, 74, 153]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6544)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .low0 (![125, 211, 228, 222, 260, 272, 269, 127, 288, 255, 268, 183, 93, 103, 127, 127, 127, 127, 172, 180, 183, 154, 225, 183, 51, 183, 191, 183]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6545)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 59 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6546)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 32 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6547)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 293 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6548)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .low6 (![91, 205, 5, 118, 68, 224, 63, 165, 37, 117, 14, 23, 233, 54, 120, 265, 142, 146, 294, 69, 202, 50, 26, 266, 152, 203, 150, 178]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6549)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 4], ![2, 3, 0, 5, 4, 1]], proof := .tail 130 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6550)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 0, 4, 1]], proof := .tail 130 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6551)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 293 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6552)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 210 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6553)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 4], ![2, 3, 5, 4, 0, 1]], proof := .tail 284 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6554)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 293 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6555)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 1, 5], ![2, 6, 3, 0, 1, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 193 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6556)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 164 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6557)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 90 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6558)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .low0 (![175, 236, 49, 212, 95, 286, 223, 36, 158, 86, 140, 254, 277, 70, 229, 100, 254, 256, 89, 264, 254, 3, 52, 254, 86, 45, 140, 254]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6559)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 84 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6560)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 113 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6561)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 5, 6, 1], ![2, 3, 0, 4, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 96 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6562)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 5, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 0, 6, 4, 1], ![2, 3, 0, 5, 4, 1]], proof := .tail 79 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6563)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 0, 4, 1]], proof := .tail 79 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6564)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 7 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6565)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 6, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 139 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6566)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 0, 5, 1], ![2, 3, 6, 0, 4, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 244 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6567)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 244 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6568)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 5, 1], ![2, 6, 3, 0, 4, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 199 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6569)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 244 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6570)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 204 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6571)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 250 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6572)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 197 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6573)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 176 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6574)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 0, 6, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 245 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6575)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 147 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6576)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 96 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6577)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 0, 1], ![2, 3, 4, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 106 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6578)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 5, 0, 1], ![2, 3, 6, 4, 0, 1], ![2, 3, 5, 4, 0, 1]], proof := .tail 46 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6579)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 0, 1], ![2, 6, 3, 4, 0, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 177 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6580)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 27 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6581)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 0, 1], ![2, 6, 3, 4, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 167 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6582)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 227 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6583)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 13 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6584)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 283 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6585)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 39 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6586)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 0, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 21 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6587)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 261 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6588)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 21 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6589)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 0, 1], ![2, 4, 3, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 107 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6590)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 239 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6591)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 239 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6592)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 239 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6593)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 5, 6, 3, 0, 1], ![2, 4, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 196 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6594)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 0, 1], ![2, 6, 4, 3, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 209 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6595)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 67 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6596)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 2, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 53 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6597)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .low0 (![175, 206, 34, 85, 260, 272, 99, 257, 190, 281, 8, 183, 133, 289, 257, 257, 257, 257, 128, 274, 183, 76, 235, 183, 281, 183, 191, 183]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6598)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 238 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6599)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 156 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6600)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 87 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6601)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 156 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6602)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 2, 3, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 291 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6603)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 219 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6604)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 219 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6605)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 219 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6606)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 2, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 129 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6607)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .low6 (![16, 88, 48, 72, 104, 169, 55, 98, 31, 135, 12, 148, 207, 168, 208, 112, 145, 249, 108, 275, 186, 102, 111, 234, 115, 136, 285, 258]) }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6608)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 195 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6609)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 80 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6610)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 247 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6611)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 18 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6612)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 251 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6613)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 137 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6614)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 6, 4, 5, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 3, 0, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 0 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6615)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 5, 0, 1], ![6, 2, 3, 4, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 214 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6616)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 2, 5, 3, 0, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 29 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6617)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 184 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6618)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 43 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6619)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 226 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6620)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 263 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6621)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 213 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6622)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 15 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6623)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 65 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6624)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 0, 4, 1, 5]], proof := .tail 81 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6625)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 3, 4, 0, 1, 5]], proof := .tail 253 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6626)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 38 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6627)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 290 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6628)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 5, 4, 6, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 0, 4, 5, 1]], proof := .tail 242 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6629)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 3, 4, 0, 5, 1]], proof := .tail 242 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6630)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 38 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6631)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 290 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6632)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 3, 4, 5, 0, 1]], proof := .tail 122 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6633)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 38 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6634)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 290 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6635)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 41 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6636)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 5, 6, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 41 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6637)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 41 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6638)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 279 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6639)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![5, 6, 2, 3, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 78 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6640)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![6, 5, 2, 3, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 200 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6641)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low6 (![271, 9, 273, 194, 58, 64, 17, 77, 173, 217, 42, 280, 132, 185, 141, 105, 24, 75, 121, 181, 259, 192, 44, 248, 83, 30, 262, 220]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6642)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 232 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6643)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .low0 (![166, 211, 230, 19, 155, 40, 126, 127, 216, 61, 149, 6, 231, 60, 127, 127, 127, 127, 151, 94, 25, 22, 101, 246, 243, 33, 295, 157]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6644)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 282 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6645)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .tail 170 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6646)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low6 (![91, 205, 292, 189, 123, 241, 63, 174, 71, 171, 2, 131, 218, 252, 119, 187, 131, 267, 188, 237, 131, 28, 276, 131, 159, 221, 4, 131]) }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6647)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 144 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6648)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 97 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6649)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 143 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6650)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 73 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6651)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 73 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6652)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 73 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6653)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 179 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6654)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 73 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6655)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6528 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6528 ≤ id.val) (hhigh : id.val < 6656) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6528)) = true := by
  let j : Fin 128 := ⟨id.val - 6528, by omega⟩
  have hsum : 6528 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6528 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard051
