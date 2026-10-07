import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard003
open N4R2OuterLeftReplay

-- Cycle fingerprint 00c117b99bcd0b2b580ce9c104d9e7c95879bea7efd414cb1fa1acc8489793cb.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 018d785c1305aa0658421b5c1ccc149f7c060e1fbea522b0bece4a1484055ba2.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 02dd4e0e3fb02433eb9c007a8eac8da91c0790df0ecfb8770f11c6040be74cd5.
def localCycle00002 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 2, .gapUpper 4 3]

-- Cycle fingerprint 03e6166d15a8d109602b932d93afeebffe6c081cb4b4c07b64200cdff50ba2d3.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 27 1, .gapUpper 3 4]

-- Cycle fingerprint 03f23581dff888ea1e571439f06a535e6154c277060cb9f5c1c8c49b0b1fb072.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 040f8e479b9e3c87f2b7360ccb9d20d945aa00f8e73e36dd944fabd5fd09db53.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 04b081a9a96dd2ffd48d06047e693eb0947fc0539e571b88705b5ddc87ce6a6e.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 081f8289bcf4e7c8be1c89d91a107f21352ce699d0d7aa26befb48d8258aa0df.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 0aab7d11782b0e818ca2677bbd92e5b73dd739aa3a42f051bee76a4ba86e34f0.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .gapLower 4 1, .triangle 2 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0b6118ca521b3333b2e9b58d5e7f63859cfa58d59d77212969336474d16d3344.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0]

-- Cycle fingerprint 0c4d148440904de055fd5d5aa05db5ebf1438a09109ecd1a14623ba7c5ce4d6b.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00011 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0cec65170e1084057ae214f971285c427bc3534f1a414c3e9c557c756bec7b1e.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0cfe579feadfba5b25f9a2a6109f8de537e975cf00e9e9f17045c7b5af70dfb4.
def localCycle00013 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 1197ad0bd9f1826a2d607492f520336a88f1a5251ce4dbf9794e4202c25cd064.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 120507979a825079b3f940cdd42e5c7120f76327d63555ca0cad714990f76707.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 12508423f527ef03f2bb502e8263e90449b457609ee0bc9b9a5ee4b6e865a8ea.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 34 2, .gapUpper 4 3, .triangle 22 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 140ab5db5a6346a7f16db39ecb6c6f33541e7ab76bb40701cc888beeb79b2331.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 166db7943b94fe23bff4b8acea1f0de214065f278da2beb9f789aeb724cad938.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1af7126f4613567ccc09039e709196d1ae51e00e6686e503c447154cde6f9617.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4]
    constant := ![-1, 3, -1, 0, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 17 1, .triangle 26 1, .triangle 31 1]

-- Cycle fingerprint 1cf40529e58ecd348f08729f700ab863b5b1f2cf1f82ba82bd38b667934f0a3b.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1d195639e1908cc911e1f7c2e0442ff899228aa8ee5e90e0555d3cb33ed1622f.
def localCycle00021 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1d617e1ea356bf82a15c5d297c933386f325afd59974fbcbe424513c3f98c3f2.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 1de8a4ec91b79a881ec817996fe9faadb045b8da6ee5a25270a24585332f906f.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1e8886f718316875ba1fb5aa87cdb2cf33b695ee1e2bdd21348fa410427414b7.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 1ed93f73d17490701f8e3c9c777789fe6d62a0ddc29d222c53cd6538fa77f610.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 21001e32fdc49ed8aae07a1d43a486d6099d8662c4447998c263b8212046b080.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 2146336cd17f53755266706d047d4582dbc6e0565936641a790fa1c0d3ab9af6.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 214e4f1d69f8be100db14176088660a7a60b3385fdd9043850f6241e3181fbe1.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 2, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00029 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 21d5ae36e49fdf50c149a61f8366764737d52f24d58cad992bd57a419cf15e7e.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 28 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 21e30366a4f30dabed3fdfd4b45be54b6bc7f0adcf8875ce677301c9293fafa6.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, -1, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4]

-- Cycle fingerprint 224bbdfd4fddd5eeefe9af3f6f7811226a52c0c95d8c26cba023571110034d62.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 247317525c75c90e752225e6b67511675359110cb50ab660a0a06009d9967588.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint 25d4afcbeb49879dac900fbdf937010bdb580d4a4af4c7a8e14b7d195cffcf09.
def localCycle00034 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 2, .gapUpper 3 4]

-- Cycle fingerprint 26c89fed1f5bd8836a944e070c79b984a16efc235e898ca25ad5871719d9bef8.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 27c4d3fae0b184e9394cffb92f2ad3dd666198055ba99ed84260a00c35d03391.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 27e350ab4c831ebe9070c4afbc59924ee0f2723e6d450b48d647e0ebb0766207.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 2866d5c9c2fd3deb246c8a505bcc1f885c0f0ae11f760d811ec8d406b833bdb8.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2a7ef10a7588637672e172cc7112cfafdf7feda94b8ee13cc44156ccbb762b7a.
def localCycle00039 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .gapLower 5 1, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 29 1]

-- Cycle fingerprint 2bba018ac58cfb2ee53b5952f36d181ab53255f7e826efde886f8b73da4d996e.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 2]

-- Cycle fingerprint 2fc01ea05d11120d73f91c966e203aeb8de3bde55d11e1001488e5967b7dc90d.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 2 3, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 2, .gapUpper 3 4, .gapUpper 3 5, .triangle 15 0]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 349c8ebd262bab22065838587466fa9b7a1765a383b0ead08762cb083e3b8c0b.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 3531274f58096a7eaef7255f22dbdc804fb10e9908b210773236416ce018ed97.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 36d9559ba100fc0be2a8cf42feb63f7a970b4189b5df917d775efc209052b3af.
def localCycle00045 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 3754687bb5fdc4a9fa8532989a0e914570cd5560c26689bbef74a7b71d01c729.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 382be7c2862699b4466a51eaf44f596802386b10da64da92ee94e3d73a812252.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 38e1013aa46c3b13df694cc09f1c4f774f7922c84d94153a764269f61b6d0b25.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint 3b222e7139f8c2a7941a4dbcd87b189788ca42c78a2fcf7f11de9a3bc809f3f4.
def localCycle00049 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -3, 0, 0, 0, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, true, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 12 0]

-- Cycle fingerprint 3b57f8067f5684b0a283aef874c3625e4f735b558251e74c60687740283476ff.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3c46f59bb84a50ff5e8476ab13531ecc5bd549423d6c681f99ec02df78cea1de.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 3c94032430d397154934ca8473ce2ed691be502ae29216a6bebc6818598e9cb7.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3e17eb09fdfa2399be3a4f7c59d1c104ed4a33df11c655a5f536527f5bbc5908.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 40352956b83a69c719c9e020c81b0bd0d8838f4e135511c9c0b69a2d67fd1574.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 434b88f42fe7dbb4654797a17d589af325c67d217b4b2c43de7a6bb055a745e9.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 44344627e4416af664b389d4409565361807bccaa9737a18c25e1b49bdb3af23.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 16 0]

-- Cycle fingerprint 44e1eabea239e7638e56ceef1648a3f5004c5efb8ed5210de9666ebb89ce1d3e.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4770d7be8a8fc5c64e163f1af1f64a8fe5a568142095d4af9af0eec017c176f2.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, -1, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint 479b679736892b89385ad3bcf26ecf325c048f6bd561627c63aa0304d41ebeb4.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 480e0c394b9eb1f3de08bfe9d3b3d5c41ca6e33cd4db0d2ac3461bf1cba83235.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0]

-- Cycle fingerprint 491c85482b92119c5e9b942d405ed14b6dc71f6151bb6cbde133e18108fac6ad.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 4b5dd22ad1b5c11f1669ccc483c98535c32d44ca4e183bd1ca6b50737df98e56.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 4cdd7d2c2a664bb2e12fd93074b3d9ebfd6f2b1ecdc626317e4b1744d4262b95.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 4e0b07999bdfb8c8ec18410c3ce7dfff9a315239ba074ace947fbaac986a27e5.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4f4331e0e94fa3bfdff9a620ffc967e2f5081bce54dba537d04c86bf1bd6c7a4.
def localCycle00066 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4f82c5ec6e5edef96eebe505d6a6e3226e6519e53605c9d218b480070c6e8ff6.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 16 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 507953c075286edbf9bcec8a2b37168a592efa77a868b861f2c65ea0801e751f.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint 50868a204e56eb51ce3b0d4f6c92cd2b5f5c49daefe7cf23fbe61293465ec561.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 515220fe0f14b6f16e5acaa584c043a44aab29921d4f070f38f6889dd824ffde.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint 51b23d8ce6360557c742de7c617fb12623565499f12c326a636224fe373edda2.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 33 2, .gapUpper 3 4]

-- Cycle fingerprint 53882514590344196e48df0be8594d29df226cc2ad4e6b17421332b46a6dd6c5.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 53b4ce8208e576e2f53eceb995e46f28e862ef7709c9fbf951914d0b66e57a8d.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 53c0a47c0940edb7eb9673f3cf4e2ce5123287629b526e3097836fff61c22f41.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 54507fcbc414d791530c1e7de2294201ce18568fe9c3d349f83b26f74d6b4af5.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0]

-- Cycle fingerprint 54dac9c019860553ac35c5d19d23fc29cfe590ddf0a85c07f43afcc1ba8be04d.
def localCycle00076 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 2, .gapUpper 4 3]

-- Cycle fingerprint 54f5e2373613048dc5e0633f691de2cd09296d2fd04c9efb90d5bd522bababac.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 58444ba9fe53c69fc27e599b181545b183797f85282f9168a5b7b133128ce4ff.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 58565b6605d7a2edf6b7652bb49688c8fdbe23bc60a336b9e70c5ee9c09598e2.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 59f80d31e201d1d73c27db1b2218fec772355c9cc61533e8a39b94d8432b7d15.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5b653f314b8cdfdf5b7a14a2e4ade751829bdb6d18c2fe4fae6a4e80f5004a6e.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 5bc19d861d9beb29f5e07c2788d426e2b3b3c66dbbeb6b2bdc3eb1809921a254.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5cdd2764d717c96c94037c7f0a2dd73fbd03c47ce4cb4808d0f47e7a1afa6aa8.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 5e2a5009708adbda57eb7df4340497d5665a895fed1920d9544fd0eae715f5fa.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![2, -1, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 5e52d4a29574d4be67238aa994a2d19aa218b52d823d0b396a16c6eb8243a1e8.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 5ef8715d8ad860a65347baa69f2d44fbfa21cf76eefeec486638694418cf72b7.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5f264e8ba9ebe05cab22cb80246bb7f9a32742e8906ec4c9a719566073cd5fd3.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 1, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00088 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 5fe049605defba570203f919ba80329deecc8600529caeb975763c8e86c5aa0a.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60a13dfb08b673103fe413356b0e611ef6f8d2f94f7b984874afbbdb49c19c54.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 60b6a069ef79a8a61dc318c7968b105cdf07c826ea0639c419d6bb6a34f24819.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 61267542e4495e14c60e65c6827fc3add68a94525397c799a4e38a9a4d944d51.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 62662e8c73ef22352267ea9c2b8077f949983084da2a6be6c6873506622c58c6.
def localCycle00093 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 628c4c0ad79eb7276ee7fa8c9204b90fc718a30f250462abd72fde8965939fc4.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 631906d683496afc13b99515f13840dda49ae2a363fc2de6ae003ac3efd61b54.
def localCycle00095 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 6413f908e8d2c6d1dd33913fdddfa57736e43c69c6c8e6350b5c1a7cd83bb255.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 1]

-- Cycle fingerprint 642baeeaac9d1d72cca1b837e1392c1087c16424b0ce552cd675dd9e60680f04.
def localCycle00097 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 671f502bcf286a19931c6a655f026ff9142ea2cca180c491bab79186ca4a1844.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6954ac31f37637206ad4ebb5f23793efbae11d93bf9ecfc8c60843ab821ac424.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 6c15d0c27904f9086aca58c892be32346d5dca3fabd57f77a90e3af0774b8bdb.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 6c5348fab51fdd6b23cf2475c300c59ca37c71d20c9e5cc1f8f53a59f050d1c1.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 6cc10ff764e3e083eb8399071027cd5f36eb250ad085ea3e60bc489010d452cf.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 6d075645e78b09d1727b1fd05be3f8c985d5d94be8200383224ee30ebe0fb442.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 6da671d9086a82c813da16a4650b4a1c9d7f8700a6525e5e6c250831d58cbe60.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 6e04082e1f86458153b176c9642ddf299f2ffa4727b76ebe45f0b2145929be76.
def localCycle00105 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6e278d69b185f8c03ee46394b6fa8bd2406420071842b7eb2939bfd4aff782f6.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint 70634aabc32595c2344102e91ffa2d2dd40c68ec1eb2da9cd2e24f6985785294.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 7151450f4eac738b8fbd7281813599e5dc7d2923b2d8d365ca2e27ec84129e75.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint 716472732a02959d41097cbc6d41390262c313f6ac016b5fdea1f4af13a9999c.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 71d086f69ef9450f0b90f0676474a73763d2a8c2ba3290c69b60f00f688c64ab.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .gapLower 2 1]

-- Cycle fingerprint 730f59a4c900131a8b057876abc1e01aca64f9d986d0fe1e91eb08a6e8378bcc.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 74a39d13d2026af91efc9dcbd2db88eb7a792a08df91d4e72a935012ff7b15de.
def localCycle00114 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 5 1, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint 752379fafe9675a470b05178f11e750d0f4f9c43017c2adbbada13114d3aff56.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7587c057a35cdad7517e74cb4662d2cc78017f20be5da163c5468f20500ae6ac.
def localCycle00116 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 758b093560ad14dc2fbc18de69cc88cede70996cca66754dfc6730ec8679530e.
def localCycle00117 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 7882eb6eb9c8dd879dfa6d628247a155a3b8979a3ddffa01018aca7be8573719.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 7abb8601372cbd27120d00109b76c25383976fe087ee09257fd962bd144dd5a0.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 7e3099c31b00e10160dc79a7acd01c5f3f8e7a7c8c5eb022ac8edc790a4078ce.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 7fa07494ac197971d658b7c4b2855b93c4613db5e7da9be7897dec323f148c85.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 7fed440a1fec8e3ab813c594ae8a58170010ac57ecf37b71f4636251f494fe1d.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 84273045f7d124f22f686249ff73cef55bd1de4da98900feeb7e5afff25d62fb.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 8479db6d307a9a165be2b16aa3b15802d38cb3ccb2177f3c264a6f3749d47d2b.
def localCycle00125 : Cycle where
  length := 5
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 33 2, .gapUpper 3 4, .triangle 20 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 856e659c5b54219f032563ae033eb5cc3038abcded61ef45255400590c3faacb.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false] }
  origin := ![.triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .corridorUpper 2 3]

-- Cycle fingerprint 8740b631315812b88bc72e10f7e5f25a0efb0e21395f2e58b092f49c5d4b5604.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 877f4b8ec78ce3773d0e3c4f52d493c38a3218bde130d09bb8cfc68e945f3fa0.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 87fef2394ef7e346ce3914d5f89a0e0d753903e8b4207c9cbf838b337925e38b.
def localCycle00129 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8829fdecf88db7c5dc4c27fb1fe6776282d2bb0d1b46af7276c2b80a755d0036.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8ab759b426a3e7803bfaada12603ffdeb6210275a12e69a3f9eb0771bb4ba9d1.
def localCycle00131 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 8c2882cc933e2b580d8e3e5563f3c496d3b57d555240470319abc86193a41b43.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 2]

-- Cycle fingerprint 8e13b6ca5cba9287ce29f8026d0d047dcab81afd7bda81db0773eb74e638fb5c.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2]

-- Cycle fingerprint 8f6bce13583a6a4401bdd35ae97f5138ba6a3f07748d6dadecf8a7b47ce0ed6d.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 9060ecaa12a71db240976474077fa00fa8e143a384c7b02b7c68e5c239b145a6.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint 91e6f9c60753e534bc57aa5d3e42f1182a4321e92f0bfab2c5c256708369a1f3.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 27 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 91f361683f8b5c564f32be1984aff4192e2e7b506b9e0576780dd79f1f70d83a.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3]

-- Cycle fingerprint 9273c6671357d83c9393aad3052ab8f54fe5aaccadff217ed7f3b5bf48bd6217.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5]
    constant := ![0, -1, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 0, .triangle 33 0, .triangle 14 0]

-- Cycle fingerprint 92cc782849f2c4ce9cbfa5cee13bd0aa61336f48f38711067dc919e73ed6e621.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 95c1caf100df4d65016a487ae5857a571c9fe144f9ba131682d46cc3cdd3d270.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 95cce7e67a7229f6b0f2bb02cdafc6b67e30fd0ab98784106fcb2453e156a636.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 6]
    constant := ![0, -1, 0, 0, -1, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, false, true, false, false] }
  origin := ![.triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 95fb0ced85a241e89dec7e07c78debe996e6f44a773c95ffc3758fadf5ffca0b.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 96bfb704c29fa0db3dc577ba1adf329b4c655d589fe9e7be720e65afc4ba08d7.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 17 2]

-- Cycle fingerprint 973f6d567d1135534acc13122e39fc4e2ec7a818389483a5accb50657177f304.
def localCycle00144 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 97f2b5b2a74233a9df39097ec0610d113527a3fd7388bf84ddf918c9684a43b9.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 4, .theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 2, .triangle 22 0]

-- Cycle fingerprint 983cc9b971e6537f99308b58ca13ec3ec67aa57116b74873a206c9a6c30e82b0.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, 0, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, false] }
  origin := ![.triangle 18 2, .triangle 24 1, .gapLower 1 2, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00147 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 986102192d0d9f4c07361568f28bdee6493867fffb983aad1fe931a04d6f6552.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 9b6a598c9db20c9cc64c33ef32e7e4e6273b56fa8570b42336b5f93aa999de33.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9b828e6cab49028ce84e20f9369d7465fa98b665f9226d466b11a8d0e41cf76b.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -2, 0, 2, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, -1, 0, 1, 0]
    strict := ![true, false, false, true, true, true, true, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2]

-- Cycle fingerprint 9c40505f868a764216facc8e987c2c4f9e496db75c7d43d46d640dcd2eb1f06f.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 0, .triangle 33 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 9c81e32b94ef650a691e35bc339e705a80ff9a7788e55e7c95135ad871506166.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 9c9cf7b56012bf0f338aeb954602ff5e2aa5024a62d6cd178a5a02cc5b1e0f78.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 9ccaecef8a3645f3a469c67cb0ef4570cd0755ab786e45070b4081e97b01f29c.
def localCycle00154 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9e3889d055b453e8176cfddec7ee7377d2239a672f3d87da3d07cfada8ecef2f.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9f763a901518418d7c72d035d5cfbe30b8482cb2146451fae1b071279f8c85ba.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a00c14c9538a435cce2fd9358a38550bc8f7422e4c81a53501f93833da32ecc9.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a18d3e52b9966216309e19a014a486343d9b119fb7e04b1843d18436f094da2d.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint a1d313d290fa39b0facc65892fb4adc043d7182c5082d811345dd355e4e6e6dd.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 17 2, .triangle 22 1, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Cycle fingerprint a3cd8b33b8dee296d867d931616b5ac604421b6af2090db8c8dc24cdcdc500ee.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint a5ebfd2850fc1da1a6c059ac537fcdfd6724b3aaccb3e362571d91c80a3f7802.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint a6ac85c8dad49f65169960ac8cea837a4d7ac4a3cc08a1e2b9a1518e30a39cbb.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a76ad3c6e58cd4d9b1f37f3e76d9be714c2363bf09df6aea464e45dd7db12eae.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 16 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a774a57eae688c8a66c2c167e1b33ad56088c5b3e6b4805e9d51bf24475334cb.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint a7ce8017f2225b14ea3f281b63670b68df0ac6b70c3706066e90eb6d23f5f7d1.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 1, .gapLower 3 0]

-- Cycle fingerprint a8780ad01977910a805f97d14e69130909c0f03b6cfb8e6d0c76a89086fe084f.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 0, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint a8b06449418b0d811a25552839611ac08ef36931cad12d25ea4e956236173732.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint a911f3386546df99c504ae862238092c642eeab0eca0b68a7387aceac7ac60d1.
def localCycle00168 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 18 0, .triangle 27 1, .gapUpper 3 4]

-- Cycle fingerprint a9552404178c49fdc38b9ef6f0874cab0dc7813e19afa891de8c2a0284dedd68.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, 0, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 32 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00170 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aa67f5357d7e8e9fb270cada6cf649bbe4e7b01edd4cdc8448f47614b7da2c3e.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint aa7e89153b21f1f58cb0df1ec7a9cf0a147579e1ce03ca8c9fa270009df9e777.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint ab18c40d4cb6e2eaaaca33ecd6603fa6da4386d36ec65f465d4ec3ca945e2d37.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint acbad68fabae1f357106d60cf43314335b5eedc7409d7712c7a54ed3db5061c4.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint acd382d353cb591b7bcbf20d3efb8f9afebcc6cdb5f7caeb07b24a6be3d01d6b.
def localCycle00176 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 0, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true] }
  origin := ![.triangle 27 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint ad2676ea14f30e356ce270f888bdbe1b9ad8efe7458505bd5e7c01a23e2fb02d.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00178 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ae334c39051365a3c58196eb8b411d4a9006798ec1ec6a577dc01a7e904f48c5.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint ae7ed2ee5f7070d66c0d0bbf40022a83dc776bf080cd7c2cd8ebd7c3526bdd3f.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint afed38c5ce6e054e90f53ad8f01fa52362af039a18b7c9345511d4aa47c7ce80.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint b09bc96bb6ceae67d0883c761191b4ddcb349e68bb620a7d76627f99d51463de.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b246538a576683c071ac5fa1166258d394913894e49cc06674eecd2d45c3e610.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .gapLower 2 1]

-- Cycle fingerprint b4778a4083686d45e0365faf3d655652be257f5e8147306429f05f96b516e3b2.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b4e4459a1ef13b1651101a165ae3a3dfe733001cc8f5e8cf35416d58b3be1e8a.
def localCycle00185 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b6603c48ac9eac8a755620596a04c29fb1b853b4a3d145082f43d3064414f811.
def localCycle00187 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 17 1]

-- Cycle fingerprint b6e5cf336b3d00499ce5c0fb19b6832d3f49319088def085cf21a0cb9389b990.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint b77c8b46654fb4e24c7b9ff2c3452b63777793d5bfd7d6786d6cd4acbba19002.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 6, .theta 6, .theta 5, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, -1, 0, 0, 1]
    strict := ![false, false, false, true, true, true, true, false] }
  origin := ![.triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4]

-- Cycle fingerprint b7d282b64a072da4b70cd21ed173fe2619736547671aa0edb1b77ef4e24f106d.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint b8dd2d9222938fb679caf3fc1d3541ad0c68ebcd6e89f51eca7c29d8c2b7afe2.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00192 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00193 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint bbda9a6aed76a4956d87de271c71c05d20c5df3d4652c02b01e6660fd0cd1cd3.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint bf3bee06dfa54e0c97e0645c80a7bd04574d4d598beb115ae1b889c83b3b3d07.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint c18d6bb33ec4c47d711ca275b16da36baf5d44730251a3bc6494ab703b21af67.
def localCycle00196 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, 0, 0, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c231b2cb3464083ac128561b308c89562954a1e65fb2a05c5768779f7c46302e.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 0, -1, 0, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true, false, true] }
  origin := ![.triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .triangle 15 1]

-- Cycle fingerprint c3bc0abcca6b6e4a708909854b6153da53514cf478269147e7ad4c3c2b6a1451.
def localCycle00198 : Cycle where
  length := 14
  data := {
    node := ![.distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .triangle 16 1, .triangle 15 0]

-- Cycle fingerprint c523925cec2a96bc8c4570346ed39c0bcd9ededffa5d27633b994334c25a4667.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c5a482e4037bd3889fe49954f1eaf81fa3a3cf86b637b188bbafad006d63666f.
def localCycle00200 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 3 4]

-- Cycle fingerprint c63ddbe1617bd217ccfc9a4e1c7129dd1d5fac5b9625e6231ed536a66a8d4473.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c6a2b96d5ec4c7a0f648c4373f5ca402b9216dc40b12d687f6f72f8bc2e82995.
def localCycle00202 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint c6fcd1c8f6fb990f2ce99d6aa287620e740b51cdd3eb354ade8578bdcb9552a2.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![2, -1, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint c828d2b9618316f3cc8be78a7d6ee0e35d94070ab19b83cbc8b31234d4752206.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0]

-- Cycle fingerprint c83d366cffc86716166e4271a50e54df0fe2295c93df061dc81ed9cd27b84533.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint c96df249fb104680bb7c313b1d9b777c53fb542fe2d49f3dbdd837b300c1a8dd.
def localCycle00206 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 14 0, .gapLower 0 4, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 29 1, .triangle 34 1]

-- Cycle fingerprint c986a308d5f430a49a9f823e70e271477051a2f0473778c4737afc4b1ea96277.
def localCycle00207 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ca549de2c8bd1ce05084dc2d3aeac9d060c95cd535042a4c44c1be0734300148.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cb19482502ab53df5f2b74c4fbbf3f3e3d6c7c1fb3da7946fd2133302384e605.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint cb4a20e41896ac38bc7530538c88fd912d3474b17aaff2acb238ca68b2be72f5.
def localCycle00210 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cbd453b2cf674fe0802a4de8308d70488a53c0cde517fcdc5e31cada6ca3dcd1.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cc5cbddff5c74c661fd28fbc52ffb83eec297f9528c59098ece004464edeabb6.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint ceeac007e830572efb1bbded8dda5c399fd343c00e110a09c88fc12554d3fbbb.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint cf6232e660c0f0a8ed6db349885acfc0534c36d5cffcde4a3f3e10a72e941133.
def localCycle00214 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -2, 0, -1, 0, 0, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint cfd7bd87ecaad83f86e3c9090da6b52f28ba53daa43261ba10338460cc7aa4c4.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint cfd906f9b714911bb13b1e8dc6aa781506a547ae370f71ec52470b491c4918c6.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5]
    constant := ![0, -1, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0]

-- Cycle fingerprint d120db563c8ccebde67ccf0f9b340cef81e0f3b25124db9bcd79fb89fe4e0f11.
def localCycle00217 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint d1d05e844354705e850575f7e40df910ef04b7dfeb6c58b7f4285ee4c4040d23.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint d2811ebc7d60e68a50a10fcba2f36aba9b20d5cf3d8c8b2d23953d964ed98b1f.
def localCycle00219 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d297af23b9c31b53664708f32449de11f2f2a8de2666d2f5963d2925eb95844e.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d5244aea8e0a152f2e20f7b5bcdf5d1a31affc5713c64030b470014cb279f2ac.
def localCycle00221 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .triangle 22 0, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1]

-- Cycle fingerprint d5a989a0aed197970196e7b3990b5da169a3ddb817203fc6c619d7b1994d1f3a.
def localCycle00222 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint d5ff2b6000262fe68923c4bb7f7ec103a5a527312abb227805c2ba88d00d8520.
def localCycle00223 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .gapLower 0 4, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint d7240fca9ad0eebeaf660d59bdf0066ecbf1c8b63197b1897c8c35b2a0e49a76.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, 0, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 34 1, .gapLower 5 1, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 18 0, .triangle 29 1]

-- Cycle fingerprint d759f10b4520d6effd09f6b19698d74b4d6f7db94bc2e5852c39242011e29214.
def localCycle00225 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d8426ac7c19a27da204bcd87d0d0004202923146f5b2e516871ffb3b2311f358.
def localCycle00226 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 22 1, .triangle 16 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint d933ad946142ad3fec6f0ebdb797894053bd7e4acd9b4ed6064fcc2f94f2f668.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint d9f3be1278dd198fa3f39549baa07e2f2da177d4debbabbf8edf17039c555ed9.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint dbd544b4eed28e3795f64e026e5dc32ae783ec6805f7124b02a379cfda623c4d.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint dc21b5a65f3233f74bb487abc3a1d0988134dc049227311a7a464bf7f5119d56.
def localCycle00230 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint dd05066571d17efc2588a65c19a35213fd1b443cff964507b9bc2275707419e4.
def localCycle00231 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint dd73eaa2f96ca0fde8b7689f4af9b7f56cf38d69be5779bf10fc26af1238373a.
def localCycle00232 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint ddc23e5f676b8f53c42044995a9f2e06162149d678593077b260d3fe6262c7ec.
def localCycle00233 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00234 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e1c9464be64f19a589d55250bc61cecfea7d1df94511dff881a3a736fabd0080.
def localCycle00235 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e1f841a8b883d0a3dd1ec567175add4c7da0fdee0e0dd293276460506cc01186.
def localCycle00236 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 24 1, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e244b74d427637f9fd1fb2780b35aa72209a3f91924b45ae092fa92884b88ecd.
def localCycle00237 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint e2f5cab7479b48ab88112698a06a189ac140747aae52df44eabedbff10db0fe5.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, 0, 3, 0, -1, -2, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, true] }
  origin := ![.triangle 14 0, .gapLower 0 4, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 18 1, .triangle 29 1, .triangle 34 1]

-- Cycle fingerprint e3378f2e014c439613e8a2e4800a82fc3586027e5d88f2346bee5edd91d47d24.
def localCycle00239 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e3ace8397b166097bc74160ab13f3ebf203049c9b3025084dae8a7fae5a2f4a2.
def localCycle00240 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint e3aea787839f5eab33d6ce6eb34f6b3c190893faef27be89c5d73ba8212e4618.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00242 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e5846869489d0e4eaca3f1d43500bcc36ca973d0e4ac6a8c79330f477ef04af2.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e58bd306be0bc4eaba63df0c1b1916ba8cd758b4f16d59a9b4d165550cc93646.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Cycle fingerprint e5b377f9776cb84f16b5904cc88165dfcc32d114d825a653c5ebed61189d4478.
def localCycle00245 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e6268d33e362e5af2177659b0aa23bcd55f15f7e34e35e0dbdd51dfaf38b0087.
def localCycle00246 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e6bbc3e30e7cab6e1a6e6715f2a9b413e05bb0cd2d4f76910820ad7cbdd18f1e.
def localCycle00247 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e7a434a761c34e80e81a640e90e83c6b58c05ceb7bff28741c1ac8a3de4f68e4.
def localCycle00248 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e813e78db01c577444132a631a93c4c532016fdb8122f7c29e356b9028996be0.
def localCycle00249 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![0, -2, 0, 0, 3, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 20 1, .triangle 33 0, .triangle 14 0, .gapLower 0 4]

-- Cycle fingerprint e87f0de43ae23f7328acb6598cd1c1364952af1042353e5df82f8a5eb18ed5b8.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint eb5a2d176d54fbf9c7717369d06c7f3b49866d4a2e6c3981e5db740d906a3b4a.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6]
    constant := ![0, 0, 0, -1, 0, 0, 2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 32 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint ed2bda85f3933f47ebf7ceae6140ea8152a6e3beb4a56c26ac3bf3462794b60e.
def localCycle00252 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint ed7a0d3a50389df90869beb76c7632a00d2da12392aaa754f708d20de046f854.
def localCycle00253 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 24 1, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint edf8e68e7be57aa95717b51805d083b40f0193c91fefe6a8ea7cb8b89687cfb1.
def localCycle00254 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint ee9a56fb3dec47a1a354884ed110d62ed5de23b340f7ffa5d2635d645957cc38.
def localCycle00255 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint f0521cbfc10c52e81c0844c917259e3b0c74f93d0ef5517207a7c29e98caf805.
def localCycle00256 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint f15feedcb085280d081e7eb429ac006f64736b6ee0291344fcacfb59cce7b53e.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint f1666bb182c17661d936fee0c378777be8ef35620c006a577529490ccecfac23.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 4, .distance 1 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 22 1, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint f1730cfe4cc2ed8d00097898db41ecbdebcf97e7719d043fb6ad3882be853c55.
def localCycle00259 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint f1fa62db4d8d99901136172053ac45bf3e2256bc1f20800c64f86f718674b7bf.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 20 1, .triangle 33 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint f4c18c9e11faa4e74735d71e9b2e51092bc28ab36c6140edb3892c5646d20878.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint f5516dd5572e3da317507bea6e77128619b73abb4698d4d89bc738da46d02823.
def localCycle00262 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5]
    constant := ![0, 0, 0, -1, 0, 0, 2, 0, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 31 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 21 2, .gapLower 1 4, .triangle 17 0, .triangle 26 1]

-- Cycle fingerprint f6805526d2e205fd53e4666f8b983282c70aed5007bf3aa5a55f4a12edc51a9c.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint f688318c554d03945d75815ae3886b40d74cc74c6eafec419ca82025e7b570f8.
def localCycle00264 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f7a2423bac1716e4f25c009a98cc2a8df627a4236b267f697ec6e4df7eccb848.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint f92027ee0263548588ffcc06f96980aa5edfad677b3666875a16b1ad7fb6e0f5.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f94d7d4475d15867b498e342e2f9478b7f082a307b6088df3802abad7eaebdac.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint fb2d5d1570c7226e6cb0591eb991155dd41681d52f340e9718a0f9454a794bdf.
def localCycle00268 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint fbcfddee3b67bbc339d692ae0818064ccc06172fbda5d4c5e3d5885fd6808b09.
def localCycle00269 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 22 1, .triangle 34 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fbf8bdc85b80422860927dcf852792628bfc83d8a53b93beda2169efd771e26d.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fcab0b37e5a31e453f05a695b900baba2660f4985283ab780b86f99dda04d57f.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fef5c9e8d1adad2d29c8b4065e9b3a5cf1384fc8f8da6da77044058e743ba8a3.
def localCycle00272 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 2]

def library : Library := fun id => if id < 136 then (if id < 68 then (if id < 34 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 25 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 29 then (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))))) else (if id < 51 then (if id < 42 then (if id < 38 then (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 46 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))))) else (if id < 59 then (if id < 55 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)))) else (if id < 63 then (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))))))) else (if id < 102 then (if id < 85 then (if id < 76 then (if id < 72 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 80 then (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)))))) else (if id < 93 then (if id < 89 then (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))) else (if id < 97 then (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))))))) else (if id < 119 then (if id < 110 then (if id < 106 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 114 then (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))))) else (if id < 127 then (if id < 123 then (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 131 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))))))) else (if id < 204 then (if id < 170 then (if id < 153 then (if id < 144 then (if id < 140 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))) else (if id < 148 then (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))))) else (if id < 161 then (if id < 157 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 165 then (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))))))) else (if id < 187 then (if id < 178 then (if id < 174 then (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 176 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none)) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)))) else (if id < 182 then (if id < 180 then (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))) else (if id < 184 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))))) else (if id < 195 then (if id < 191 then (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)))) else (if id < 199 then (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))))))) else (if id < 238 then (if id < 221 then (if id < 212 then (if id < 208 then (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)))) else (if id < 216 then (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)))))) else (if id < 229 then (if id < 225 then (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none))) else (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))) else (if id < 233 then (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))))))) else (if id < 255 then (if id < 246 then (if id < 242 then (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))) else (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)))) else (if id < 250 then (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none))) else (if id < 252 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id = 251 then some localCycle00251 else none)) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)))))) else (if id < 264 then (if id < 259 then (if id < 257 then (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none)) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none))) else (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none))))) else (if id < 268 then (if id < 266 then (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none))) else (if id < 270 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none)) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 99 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 384)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 77 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 385)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 6, 5, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 22 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 386)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 220 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 387)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 5, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 77 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 388)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 6, 3], ![0, 4, 1, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 6, 2, 4], ![0, 3, 1, 5, 2, 4]], proof := .tail 118 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 389)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 1, 2, 4]], proof := .low (![67, 119, 186, 272, 170, 71, 79, 46, 93, 215, 236, 34, 37, 95, 164, 125, 34, 151, 66, 95, 34, 95, 161, 34, 230, 34, 28, 34]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 390)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .low (![67, 119, 186, 272, 190, 217, 0, 46, 93, 215, 13, 249, 203, 95, 164, 271, 156, 138, 66, 95, 95, 95, 161, 63, 230, 56, 24, 260]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 391)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 108 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 392)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 6, 1, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 68 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 393)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 2, 1, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 178 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 394)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 2, 1, 4]], proof := .low (![110, 265, 113, 242, 64, 217, 0, 259, 20, 173, 101, 184, 203, 122, 82, 132, 107, 138, 257, 73, 65, 252, 261, 218, 176, 227, 169, 251]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 395)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 1, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 191 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 396)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 1, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 178 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 397)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 1, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 54 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 398)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 154 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 399)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 51 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 400)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 1, 2, 4, 5]], proof := .low (![183, 174, 29, 187, 147, 245, 268, 112, 270, 267, 155, 214, 11, 211, 100, 143, 61, 123, 32, 142, 241, 167, 4, 85, 33, 106, 262, 141]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 401)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 159 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 402)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 51 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 403)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 1, 2, 5, 4]], proof := .tail 86 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 404)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 3, 2, 1, 4, 5]], proof := .low (![30, 174, 29, 19, 88, 168, 197, 112, 102, 171, 111, 3, 11, 133, 194, 128, 3, 123, 78, 166, 3, 146, 179, 3, 126, 3, 136, 3]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 405)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 3, 2, 1, 5, 4]], proof := .low (![30, 91, 202, 81, 88, 168, 197, 60, 35, 171, 111, 3, 11, 57, 194, 128, 3, 177, 58, 166, 3, 7, 179, 3, 126, 3, 136, 3]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 406)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 1, 4]], proof := .tail 200 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 407)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 1, 4]], proof := .tail 10 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 408)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 97 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 409)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 4], ![0, 3, 2, 5, 4, 1]], proof := .tail 213 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 410)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 6, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 2, 4, 1]], proof := .tail 10 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 411)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 213 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 412)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 69 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 413)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 69 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 414)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 1, 5], ![0, 6, 3, 2, 1, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 53 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 415)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 416)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 145 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 417)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 6, 3], ![0, 4, 5, 1, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 92 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 418)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 36 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 419)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 231 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 420)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 153 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 421)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 5, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 233 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 422)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 2, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 135 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 423)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 255 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 424)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 2, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 41 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 425)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 188 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 426)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 114 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 427)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 428)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 210 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 429)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 210 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 430)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 104 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 431)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 130 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 432)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 62 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 433)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 47 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 434)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 153 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 435)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 158 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 436)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 2, 1], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 48 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 437)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 210 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 438)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 165 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 439)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![0, 5, 4, 1, 2, 6], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 105 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 440)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 31 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 441)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 148 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 442)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 205 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 443)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 45 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 444)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 178 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 445)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 232 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 446)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 199 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 447)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 178 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 448)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 199 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 449)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 450)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 43 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 451)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 2, 1], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 243 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 452)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 2, 1], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 244 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 453)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 4, 5, 6], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 201 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 454)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 4, 5, 6], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 264 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 455)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 38 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 456)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 89 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 457)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 120 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 458)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 248 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 459)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 196 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 460)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 94 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 461)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 248 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 462)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 2, 3]], proof := .tail 27 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 463)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 2, 3]], proof := .tail 247 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 464)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 235 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 465)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 6, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 74 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 466)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 4, 5], ![0, 6, 2, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 149 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 467)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 5, 4, 6], ![0, 1, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 225 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 468)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 5, 6, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 59 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 469)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 6, 5, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 239 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 470)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 5, 6], ![0, 2, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 50 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 471)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 127 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 472)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 198 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 473)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 44 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 474)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 219 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 475)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 139 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 476)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 116 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 477)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 6, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 189 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 478)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 4, 5], ![0, 6, 2, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 152 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 479)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 4, 6], ![0, 1, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 180 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 480)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 6, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 221 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 481)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 6, 5, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 12 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 482)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 163 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 483)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 109 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 484)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 137 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 485)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 226 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 486)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 129 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 487)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 207 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 488)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 185 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 489)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 1 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 490)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 223 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 491)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 237 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 492)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 134 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 493)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 4, 6], ![0, 2, 1, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 72 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 494)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 25 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 495)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 240 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 496)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 229 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 497)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 182 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 498)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 5, 6, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 266 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 499)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 80 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 500)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .low (![49, 193, 131, 144, 170, 2, 204, 234, 98, 55, 253, 76, 70, 117, 55, 16, 76, 209, 5, 117, 76, 117, 150, 76, 222, 76, 87, 76]) }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 501)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .low (![9, 193, 131, 144, 17, 256, 263, 234, 98, 55, 103, 269, 84, 117, 55, 254, 250, 216, 5, 117, 117, 117, 150, 21, 222, 246, 121, 258]) }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 502)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 23 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 503)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 42 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 504)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 208 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 505)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 2, 1, 3]], proof := .low (![8, 175, 192, 242, 64, 256, 263, 140, 6, 14, 212, 228, 84, 90, 115, 162, 96, 216, 15, 195, 124, 40, 157, 26, 238, 206, 224, 39]) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 506)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 75 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 507)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 160 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 508)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 509)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 172 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 510)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 83 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 511)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (384 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 384 ≤ id.val) (hhigh : id.val < 512) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 384)) = true := by
  let j : Fin 128 := ⟨id.val - 384, by omega⟩
  have hsum : 384 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (384 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard003
