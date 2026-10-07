import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard035
open N4R2OuterLeftReplay

-- Cycle fingerprint 0000caefad90de777ba49f8e00e7859b33b3ca1a2bc812c35988046c7dc6ee1c.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 00f76a4d51c1d73aa5429d18e73be3dcb12ab83b69f8949fddd73f69bac26036.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 0186cde1ba2091ea5ad41ac7327a986fec34dcc878691752cfda83994a7bbabf.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 02a05babbb5076de51e5d00c96a149f0a6997465dd64c92fce5b661cba47c2f5.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 040f8e479b9e3c87f2b7360ccb9d20d945aa00f8e73e36dd944fabd5fd09db53.
def localCycle00004 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 04b081a9a96dd2ffd48d06047e693eb0947fc0539e571b88705b5ddc87ce6a6e.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 04c51e5e362a3f6985db3e6b67258da10e8f716254f5ae80006fd4026dd09e20.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 4, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 04e895c6ec11c24c427778a040b61044e66e66b0bad671d2836b6703d98e3f5a.
def localCycle00007 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 06e00c51d7d794c061f6544d4ec1a7c3233c15d3bbf723242f8c12947d175348.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 0872f0e0a856b9f4e457d1751de2ece7cd4492f6ef8177158d2d5e2644899cc0.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0b0bf87c379c94a4521df914c045cf0504334243c2d61f6ce97ae6d51122ba05.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 2, .triangle 17 0]

-- Cycle fingerprint 0b2e7c8f813b043fc0adf381a89549a8cc7fa6f4d5798f84707fd1d7cd3b28e5.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 10326e20ef947fdde0b257b8777eabf09114c975cd010ca5edffb35ef171b1fb.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 1197ad0bd9f1826a2d607492f520336a88f1a5251ce4dbf9794e4202c25cd064.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 11a06cb40c06cd5a64fce2c71eccd4303eb8fdc7b68bc273f0f96f01bbdc659e.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 120507979a825079b3f940cdd42e5c7120f76327d63555ca0cad714990f76707.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 15ffda8b272e42a0b901fe3efea4a89c6d8ed9d42d289044ee0a24731b52310c.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 181eb11416e1fe676ad3f8b0bc69a2350be83200726d60e90158de3ba7235a65.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 19645b0058b1fc416cee981fee43da21990802d6a9cef66f66ba4be86dcca281.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 198fedc519c1a39e4dd39461d8f78926ec1fcbe20dde7edc74dc5d982d8d2f22.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 1a853033c57653fab45aa35b04dabeacda054283dbeef60788349a5121ef7f4b.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 1cbece66b0ce944f38c541383a87237b1bf4e6b07f08b3781626037b5ebf0306.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 2, -2, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, -1, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 1de8a4ec91b79a881ec817996fe9faadb045b8da6ee5a25270a24585332f906f.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f0f11a7570d8978f257ec6bdcef3dd26c79285a8ad33aa4d8b858bf0c547e40.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 1f7041fb84635be0fa2e9ef672bb9eb31433111d32032a313e49a2ebfd9d3270.
def localCycle00024 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 21001e32fdc49ed8aae07a1d43a486d6099d8662c4447998c263b8212046b080.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 235237ae1fa971193162c7f5ee56d12badb500544ee83a0e241876807c593b38.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 26f6341df2e33c7a15b91f111fafa7adf7cf30646e3cfadda7b73496ad45365d.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 2909974737b0ff7a0fc4e5a2906828a65b3b47d1379731298a475ceaa028cb91.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 2983f9d08a0ee8368620928d553ccdc79f3b5505f86ff158407f13927aaceb77.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2a1124a087af58b1b7f3493ccb1740cf4e8b94b95c3e88cde34e85c787a82e80.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Cycle fingerprint 2a3b0dc9d20b500d89dccd18f9f8e7b93a51068936334c8c1e818cae98c91ebb.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 5 6, .theta 5, .zero, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 34 0, .corridorLower 5 6, .thetaLower 5, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 12 1]

-- Cycle fingerprint 2bba018ac58cfb2ee53b5952f36d181ab53255f7e826efde886f8b73da4d996e.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 2]

-- Cycle fingerprint 2e3c75cfc75b0aa35a54f21f91e98a10ee2c7beb889ad2539d512fc3ced3bd20.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 2fcda4cc768318671661c28007d784e1bb2001e5b8df2e759734f53b158febe2.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 32d2b9ac4d7f1dba336ed2cbee7570c261f17cdd91a69512cef811434389280f.
def localCycle00037 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 336b59420a2e659b178441175c930f26636bfa91207a9f0af30a1e3ff1e7dba4.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint 353c4a3112efb16a5e1067297a6a6f54bdb0bff79453cebbf4da7e339ea50f7a.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 35af2576efee34f3a4273d59c10e928b155d7e85ffb3d9dff61c898df893dcf2.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 8 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint 372cf848aee3caa73e84660bb15c1ea6c7cd195fff955e30de43f1b1a5c9c407.
def localCycle00041 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -3, 0, -1, -1, 0, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 38c598d866eb75db5f9a51ba6687c3527c6ba1f4a8f04702f32ef23bb1a2222f.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 3a39cee49b7fc045b398757c7aca0739bd0096e53a400f54de9b2f5216760a39.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3d3d81ec50b241b6abcdc8a41cd598cc665716326b2af597a8117a984993e4d5.
def localCycle00044 : Cycle where
  length := 15
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![0, -1, 0, 0, -1, 0, -1, -1, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00045 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 434b88f42fe7dbb4654797a17d589af325c67d217b4b2c43de7a6bb055a745e9.
def localCycle00046 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 4414ebc9690a0577378d74bd4ddc95ecf5fdb3b2c3c7e48919af789ac59eaa02.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 46158660cb1bf3014891bab79f4b1ae5d2d387f708d277f41e334331e08dcb00.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 29 1, .corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 47dad1ee5f0782910928be91a19498503cd5dac5e8394503f1133d1818218aa0.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 496bcf4f7e756b4462aecfceea1261b51a70776181a0b8d3b20e1d7ee9916978.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4, .distance 3 4]
    constant := ![0, -1, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false, false] }
  origin := ![.triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 29 1, .corridorLower 4 6, .corridorUpper 3 4]

-- Cycle fingerprint 49d136066e3aa49416c03aca0b0be5cc0652c93c82a3f0201a8737057445001f.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4a2b26d19868824859f09c16ec28869bdefd3f312d4b05c7a5236969e9057335.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4b497f37778c4a7c918cdb63c5447c7e997254e43245c3d5452efffc13a99f31.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 4cb1ef75e918b9a3673a3606734f7d8d911f7a6362da060bd5c0380e3906fa0d.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 4ccc17231d250d014557ae667fc7a8d5d942b039b19a30d2b5fc6a9bfb979e9b.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 24 0, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 4d2b559c9c4243a595a0247f7908f1f41fae7ea09c42e3527e07b4c76adc1062.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 4ded654a376871fe12fd222ce042ac58d3dd50f7e38c4fa3af4ce96f28fee8ed.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 15 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00058 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 52e2c8a788023c83f597a34b07236b19a3eb3d78f508071fc195e2c80d575f25.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 23 2, .triangle 24 1, .gapLower 1 3]

-- Cycle fingerprint 552196dab77dc1f823133082f53bf66a7726bb0f11299d5fd001fdf37bfc0f00.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 21 1, .triangle 1 0]

-- Cycle fingerprint 5688041c2897fabd5e1d18bec7917bf27c271dd438e7648dca46a1d14a31414b.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 57d41a1c2f2a58165e79bde46e6cc84eee138643eafbe7c0fc703a85b73afc78.
def localCycle00062 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 5ad3d33542770b243a0504ebb1d58970490656e771648ddc55fedff571425447.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 60a13dfb08b673103fe413356b0e611ef6f8d2f94f7b984874afbbdb49c19c54.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 60a1f65e3ae1febe338c5a3563ec4a48960d124856126a62f0a53e0d1e86928e.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -3, 0, 0, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 4 2, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .corridorUpper 3 5, .triangle 26 2]

-- Cycle fingerprint 6344f98fcadc2ecd73d6acf1ab94fd5be90cb2eb60315b0f29dff4d235ebb173.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6413f908e8d2c6d1dd33913fdddfa57736e43c69c6c8e6350b5c1a7cd83bb255.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 1]

-- Cycle fingerprint 64eb3dcb22d17b6e5e595c9106c7114186920bb8e3362564c5e2eae19baaa021.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 661cf3f97ef86a4463d8005536598ced8d2782fee9ebfa536ec32ae3d48837a7.
def localCycle00069 : Cycle where
  length := 14
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 671f502bcf286a19931c6a655f026ff9142ea2cca180c491bab79186ca4a1844.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 676387c4384271c620c55ce1bd4be5c04791b79cc4e1d4ecf298bca5a003c001.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint 69b4806ab9b456a8f418b3418935803401636b91aa0a0feade4ab913528fed2d.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 6a79e1143e46122d4e48d03ab05851d4534fd854ebca74fb506188564fc65d91.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6ad2a0fcfe544557095664e2953c7b3a6c53cfb862a68a77de7c3576f1bf3b0c.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6feb052de8cf1726fdaa7c7d58b4af20c27edc76be0deaf1b7b2ff84a8405b7c.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 750abb8493db1edfacf33bf4ba058274df1ec54e12249be22a6ca970ec42206b.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint 752379fafe9675a470b05178f11e750d0f4f9c43017c2adbbada13114d3aff56.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 758b093560ad14dc2fbc18de69cc88cede70996cca66754dfc6730ec8679530e.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 76935e1c48a121690798aa1cb861bb4bb7a8f6ba8eb9dcd87e997f72dceb2f8b.
def localCycle00080 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 78771434bd30b2ee7159f616d3dcb16531d38a988cd29a3230e9bf9148be9567.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7d05747694101b4f5a8e5bf2d59abfafec35f2ab35f3fa32fca97f1ba73d7f75.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 7f14c76e45a64b4a0fb11eb7e0f6ee4c82cdd5891d9ad214dc1e511a82d4e951.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4, .zero, .theta 1]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 12 0, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1]

-- Cycle fingerprint 7f37e46a51143079acf19a0f9410809587497d6305686c3cded5e40111ef1ba2.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5]
    constant := ![0, -1, -1, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 14 0]

-- Cycle fingerprint 7fc8e7a61c5cecf8854f3467b664078917fcf4e30c58a473b9df0172fbd88f39.
def localCycle00085 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 17 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 800d91df492d3c4fa8bffb3098c0356b8d8ee23a9276ebf2da9663b57b4c3a54.
def localCycle00086 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 8218c1744c9bac7e81133baa44634c24f277fff6b74e2c11d8ebd0ee8d721379.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5]
    constant := ![0, -1, -1, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 14 0]

-- Cycle fingerprint 82190763a960bced7b82708ed585d179b5d77d9afa3baca2d80a2e30c7eb71d9.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 82b45b80c840c636f21eb383670da444ad17699961e20f97da302437ff6fa67e.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 82be1e7f53307314651cfb89dd08c2a8ed5ef12b1efb761a3196715952c0ed9d.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 84273045f7d124f22f686249ff73cef55bd1de4da98900feeb7e5afff25d62fb.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 84730b3ef4ffe134d5401be22ad5f1c5cfff72b4a22361885ac3bcbe76b5f6f6.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 85f77edf0847987cf8f7d450abb2cad6cb6bbcb3b26a163b80036fb61840ea0f.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 0 0]

-- Cycle fingerprint 8695e95c3d9b42b988f1f331e1fa48b928e1a5096df25261257b471e968065b2.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint 86dbe340c6b6ae3b3540d6bb4e8ec0e3ffbf68d9543585a0df91fd214d579520.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0]

-- Cycle fingerprint 88ebec1ef3863da88af25d5cb9de66bb66d64fb55f33aa85f7a4bd7815575ce2.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 89a85ebfb54a9c0d9c209cc008fea705dffca589a418052f6b9c3758360ab4ee.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 8a7072d912d64296c76ed1dc7db5df50e19dbfa9a3f26e6145d7f2bbee6a459e.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![-3, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint 8cc7e5634b46fbe9209510ce43ee4e7d18cd49d5b2969628a6dc814ec368f287.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 8d8d26605ab27b18bf3346f43aaa631abd34c33d9e3fa0ec529ab9862678d84b.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 8f5247b3e8e57fe414304ceb5f51e87e358ee63940de5540e2f4ce8d5d06d22b.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 921e379cf220a8d3b00ec49b190a0cb9bfa9789f90ede3eb42f2825f7f5f3a57.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 92ca72f0bf1c4af4451f51e41307a0f5005db2d57a00ddfe4ad0771a4ca3b866.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, 0, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 931fa9d60f62b627c27b9ad0f790d3ba71effab18bfb438e1d29203507d1efee.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 947b4b7da31d6582238fe0d39565c0b6853893c6b154eb99fe2b5d27e07e0e20.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 95c1caf100df4d65016a487ae5857a571c9fe144f9ba131682d46cc3cdd3d270.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 970b46a49e71969dccdb3127d6767fc2df3e1745944b78c1ba3f4f3166294dff.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 973f6d567d1135534acc13122e39fc4e2ec7a818389483a5accb50657177f304.
def localCycle00108 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9b3df5ae7711b3c19369aa4a6abbcb3a4938d70ecdd7ca7db96b53752bfd5cd7.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9f741d72cd9feb30f0f718296912c06d93d99e9c48a42fbc52e068d221786837.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 9fa6f58a2e10acaafca188e0a2b2bb3254b6b6fd28b294100272e8ee975ffd52.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a00c14c9538a435cce2fd9358a38550bc8f7422e4c81a53501f93833da32ecc9.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a0539aa6e30f87ab70835cf21df4306c123b979c460216721f0053cb72e96093.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![2, 2, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint a4d2b2c0e88503d2088bef9043d637df967841dcb9b75bf6cc0658ceb659b1e6.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint a4d6e05aeb6857f6e0a0f221a01b059480827d435846887402efc04ae464a51e.
def localCycle00116 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a57e7fa79ff3b55eb07266e63ff2462a190f03c54a335a40dfe5e78ecaaf7833.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint a6ac85c8dad49f65169960ac8cea837a4d7ac4a3cc08a1e2b9a1518e30a39cbb.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a8cfeac4caf644fad40e2e5f1ae2726d1e91e45568df9cebdd6e062e41d69f1b.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![-2, -1, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint a9fb253b3f30529820911977a70afd83cae655e87af8b9ad8718bacf95afbd34.
def localCycle00120 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint aa57485b10a9d34fe62af4f8698a400b8a5df86272db25d030b7bb0572c6a1f1.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aa7e89153b21f1f58cb0df1ec7a9cf0a147579e1ce03ca8c9fa270009df9e777.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint ab5b2a9c6057a41b3989e5ef1765f5c586a651d19b415cbdf618601e0a80d5bb.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint abf42161645a9dd044edee6ddd457810b1242d2a909e834e36afd3f96fe2593e.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint acbad68fabae1f357106d60cf43314335b5eedc7409d7712c7a54ed3db5061c4.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint b045b8ac1ed0023e9330d11e32b564a5f7ecfbca7d9a6e850e78a2282fc4d8fe.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b0746369f46b1f811b26c199f46d782217d4f5ba0c30f114860efe6913bd9b67.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint b0a9c85a3c5b2f98757c8dc26868cfc9aa8cd2f2733c2b4839a5f118fdb84b19.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 24 1, .triangle 34 0]

-- Cycle fingerprint b0b5749a630f0ec269c964cdda0959968693f5918becda483fe343c925463745.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint b0cb6bb12a31305ccad3962da308b33e93f67a8c0081d9d062d3cf4e0630a604.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b1e84b055b7d426d8eb85496d68966b0bb7ae78d8d2803c9d12ac8e8580b85ba.
def localCycle00133 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint b1efe193482065051245aea45ee71c4d123329c275afae7ffd0a8571fa200024.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint b2258e091407d8f87f336eb34bf2078d8f38bca77dd80f5d5e91e7f68999b22a.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint b2b6266edb92e2a2af1b577c008da24c28807ae113fe5db1dc75d93b186e958f.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint b34cfb258bc4b3b905e856b1398f38efd94f4c24081476c0be74fde84e8be09e.
def localCycle00137 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b53c2842acbf8a2a7d8860c0fa77cb043f600d13fd8a0e0aba79b259bd846780.
def localCycle00138 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b896e22247e3c1a228b02cd2e345a3ac8028e271f9199359165b4be3cd4a8309.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint b8d769dc81442bc402bad772da6d8378fe6a7e05ef02f76c45b31826f3aedc56.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b9ddeb734db6244834047858d4736d11c8bed434c1e4481bbcc8acf8865e83d7.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint b9deef31c796eac250ae6d196a071d02b7796bb64c933c441321f74d32a02b37.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .triangle 24 2, .gapLower 1 3]

-- Cycle fingerprint bac7c6dfb32f4f95fd274299f556a098b55b71d74da5a85053a25374b1e298b0.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint bb0c4604c1ff2f5a6439d7852b0454e86daa3a4f8eba5daefc940b023de28a77.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint bdcae35e63175e33b2783346d4b857388064ab86100a87e84a2a6448c23f6e85.
def localCycle00148 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint becaa9c0ce057a273cab94b84f07ed5c8a3de170a38547ecd432b6edcea402e4.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint bf3bee06dfa54e0c97e0645c80a7bd04574d4d598beb115ae1b889c83b3b3d07.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint bf3ce67ab7df63f40e52956ffc01d132df0905011b4852d7f7427691b3f7a04b.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint c0a2035eb1b13e76be3dbeb26d36cc5d7ca06e61c0ccaee7d0bcd1d364200097.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 3]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 0 2, .triangle 5 0]

-- Cycle fingerprint c18a6b0fae36e432cb67362bfe0478177911105d8c24c744ff3a2640512167ae.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 14 0, .gapLower 0 3, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint c28b5989989bb38f0adf33b38bd62bf307a8b06408560dbe5f1c7b8d620afb26.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint c2d6bd694501a21a877affd7a766de7b014989daaf411584788ec70133d708bb.
def localCycle00155 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 15 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c4cfe4dd66d977d67f6139d5fc334aae32079b6ca3a75667fe8ee6e265a17049.
def localCycle00156 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c640849dcc36685d080b3e41e2e4b341a30db88837ce48550ea16140f27f637a.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint ca4879519bef51dc8172b75a686ddd3a8d3f4295ccc1b029d82554173934edfd.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5, .distance 5 6]
    constant := ![-1, -2, -2, 2, -2, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint ca6c704cfacdea34c5c093564587875cf841512611c1a8c543d0d42967ec22e6.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint cbe8ea30f2b29688614bf2c6dde7e8d36c50564539b51048daad9bba1b79d719.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint cc08ea4155a4933b9796a3946007cde08334c00ba14285349aa27747f2e0f7e1.
def localCycle00161 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint cc5cbddff5c74c661fd28fbc52ffb83eec297f9528c59098ece004464edeabb6.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2]

-- Cycle fingerprint cf4cb8852856f0255c0988ab0650dcc470b3a5d79159c5bd45a1179fc653cbe2.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 3]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 0 2, .triangle 5 0]

-- Cycle fingerprint d2a17b5ac9b04c2fde1f9e44ff695cdfb1bb8c8f07071c6e6360e5989213ef5c.
def localCycle00164 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 3 0]

-- Cycle fingerprint d3ba7269eb61fc46ae17f54514142eb1d3890d40c3adcbf64bbaa33f9ce4ca4a.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint d45f55a14ee15b5a1b537db7ee9cf4aa6872e4cd75f84d10b48cf9f8d884b369.
def localCycle00166 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint d67b53d315e63524387d721f2d3c4a6e809b167f1aae85e512860859d0e9411d.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![0, -1, -1, 0, 0, 3, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d7885923ecd5b8cfe0f37841061abc621ca66d842db4164f3c802120423801ab.
def localCycle00168 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d962719783e0852bf3c7b08d7212e87025eb907f52278ed65dd77ee4db4086e1.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 6, .distance 0 5]
    constant := ![0, -1, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 13 2, .triangle 14 1]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint da670410d0cfb66e5695cdcbb36edde6b98f60a574a9d77d2537164fad5c543e.
def localCycle00171 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint dab56ab642fc668c50eb9a08c375bfc9119da5e5e72b7ef93a05eb10fe05db19.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint db55541d4ac56078e3cb012029561c24178d970e80335890b5d45632e2b12e01.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint dbbeeebe01676b3b6f41d022733411becd83f35f6bcae398aff573a25cac4ab2.
def localCycle00174 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 17 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint dc68496056b7966e9d23a2012c90cfbd13efa080d128fa97f24881739028c4e9.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint dc950f3f9a8603bb9268749ebec4bd504bdd907ea4f743c7fad806f5a2514945.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 24 1, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3]

-- Cycle fingerprint dd0ff7313879b2eafa3f9f66052f13236ec4bb628389f6170bd4e5af2ef9ca1e.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint de3f3e0db286105099ac83a2d385436e6896f5ca103158da58382b26589ae8aa.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true] }
  origin := ![.triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 23 2, .gapLower 1 4, .triangle 3 2]

-- Cycle fingerprint decb571c310c0e2e65f3092dd8a598614913a7c09ae306da9d8b2b9335b92ec8.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5]
    constant := ![0, -1, -1, 0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 22 2, .triangle 24 0, .triangle 14 0]

-- Cycle fingerprint e0db84f3030890c2e2429302161c85709153ffe83f3ea5af7005f4403e72b6cb.
def localCycle00180 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 24 2, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00181 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e25c4fcc6b36ca05adbd3f1de47b5ffecb7c012113092cc4e18755e938fe4815.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint e46c5ae4dc96cbfb9a85a99fdef667540ea7c58a7bab458852b737896a991282.
def localCycle00183 : Cycle where
  length := 6
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6]
    constant := ![-1, -2, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4]

-- Cycle fingerprint e60a4ea004ad2492f2bf62e63a0ca6f5ed54994a73c3555342c585119d0c34a0.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint e726db0cc86c926b9ae1b914535bdc0d53a84949f68ede6f7be9986a8a7e2681.
def localCycle00185 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![0, 0, -2, 0, -2, 0, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint e74cbf4d7bb3c5f470613b748721e9173d36fcbea947119b2c9f5a9736edda33.
def localCycle00186 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 17 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint e7d02208e286580586fd9ccf7a3038034049e63a8d614fd6b2ac76c981bfe657.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 24 1, .gapLower 1 3, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e87f0de43ae23f7328acb6598cd1c1364952af1042353e5df82f8a5eb18ed5b8.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00189 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ec846b2c4e33f00df78dd8c2bcfad49e8f042dd103d959e0cb635a19d6ea7d2e.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![0, -3, 0, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint edf8e68e7be57aa95717b51805d083b40f0193c91fefe6a8ea7cb8b89687cfb1.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint eeae81c34cc2ea2b5b8beb37542721114255d1d599a4b07170538db175d7a9c8.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Cycle fingerprint efa35e33546f79c3149dd53e2e7507bbe5a20ad5233ebdf167d5a37b15ce11b5.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint f04cb18456e158e0de2705e31baf9a17e759c8cf31a5ebfaa5b2b1d39aea971b.
def localCycle00194 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 3, .gapLower 1 4, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f0e3867de1f5237d715afd32546fd068dc533fbfddd993007b217b72d49adbe2.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 6, .distance 4 6]
    constant := ![0, -1, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 34 1, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 29 1]

-- Cycle fingerprint f25cf8b6e16620305b6d2259d11c46ed2c80b724b5a0739b4138186c5d9c66a8.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint f2e226e1c7b72d46950646c7b8a4a2d8aa06b6fb839498a565a0fdd3b55abd6a.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 0 0]

-- Cycle fingerprint f424fdf0da52ecf2ff00ad4f55ee9ec4a728c465eaddaed77b28ca3149f7438b.
def localCycle00198 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f54e85106932ecbdf083157146394d0fe29b12cc4397c7fc7d4b060c11dff696.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint f706ca34d125419d24ebef62212c4c46f4cd59143569a74ecd827dbf6266db1b.
def localCycle00200 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint fcfbfb229ed28f32a13b524abfe62db9192dcc986f4b7ccbadbedf075aeb0b60.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

def library : Library := fun id => if id < 101 then (if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 88 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 94 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))))) else (if id < 152 then (if id < 126 then (if id < 113 then (if id < 107 then (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 110 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))))) else (if id < 119 then (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))) else (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))))) else (if id < 139 then (if id < 132 then (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 135 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))) else (if id < 145 then (if id < 142 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))))))) else (if id < 177 then (if id < 164 then (if id < 158 then (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))))) else (if id < 170 then (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)))) else (if id < 173 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))))) else (if id < 190 then (if id < 183 then (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))) else (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))))) else (if id < 196 then (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 27 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4480)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 27 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4481)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 51 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4482)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 7 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4483)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 14 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4484)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 123 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4485)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 86 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4486)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 74 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4487)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 33 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4488)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 69 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4489)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 148 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4490)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 9 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4491)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 9 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4492)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 104 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4493)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 151 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4494)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 171 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4495)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 37 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4496)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 151 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4497)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 171 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4498)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 159 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4499)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 159 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4500)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 49 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4501)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 49 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4502)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 49 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4503)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 49 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4504)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 49 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4505)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 165 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4506)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 138 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4507)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 123 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4508)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 44 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4509)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 97 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4510)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 62 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4511)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 112 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4512)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 104 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4513)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 35 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4514)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 202 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4515)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 135 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4516)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 177 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4517)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 20 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4518)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 20 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4519)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 131 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4520)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 76 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4521)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low (![17, 107, 80, 133, 114, 41, 18, 11, 201, 182, 6, 132, 139, 196, 96, 168, 73, 125, 85, 56, 174, 174, 167, 185, 187, 52, 164, 83]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4522)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 89 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4523)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 28 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4524)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 19 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4525)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 175 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4526)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 94 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4527)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 88 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4528)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 129 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4529)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 192 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4530)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 23 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4531)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 2 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4532)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 172 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4533)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low (![10, 189, 80, 133, 115, 92, 100, 126, 43, 182, 8, 184, 45, 110, 186, 117, 136, 170, 85, 174, 174, 174, 154, 163, 59, 26, 178, 147]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4534)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 200 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4535)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .low (![141, 103, 72, 55, 120, 92, 169, 61, 140, 93, 194, 71, 45, 110, 155, 180, 136, 57, 158, 21, 79, 79, 68, 183, 183, 26, 178, 147]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4536)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .low (![95, 143, 72, 108, 122, 98, 84, 181, 70, 197, 157, 119, 153, 79, 46, 173, 119, 179, 4, 79, 119, 79, 161, 119, 145, 130, 176, 87]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4537)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low (![95, 143, 72, 108, 190, 38, 82, 181, 70, 197, 1, 144, 45, 79, 46, 191, 144, 12, 4, 79, 144, 79, 161, 144, 145, 42, 99, 137]) }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4538)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low (![95, 143, 72, 108, 77, 16, 105, 181, 70, 197, 1, 111, 45, 79, 46, 191, 188, 121, 4, 79, 79, 79, 161, 152, 145, 81, 99, 31]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4539)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 22 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4540)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 22 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4541)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 53 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4542)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 36 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4543)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 36 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4544)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 128 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4545)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 24 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4546)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 36 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4547)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 160 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4548)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 124 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4549)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 0, 1, 3]], proof := .low (![193, 127, 142, 65, 58, 48, 105, 106, 5, 13, 162, 60, 45, 64, 78, 118, 67, 121, 15, 150, 91, 32, 113, 25, 50, 195, 34, 40]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4550)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 198 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4551)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 198 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4552)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 75 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4553)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 134 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4554)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 30 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4555)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 33 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4556)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 146 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4557)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 156 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4558)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 0 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4559)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 66 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4560)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 90 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4561)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 90 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4562)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 104 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4563)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 151 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4564)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 37 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4565)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 151 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4566)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 0 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4567)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 66 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4568)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 39 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4569)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .tail 39 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4570)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 104 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4571)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 151 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4572)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 151 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4573)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 159 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4574)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 37 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4575)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 151 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4576)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 151 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4577)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 159 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4578)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 54 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4579)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 54 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4580)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 54 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4581)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 102 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4582)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 101 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4583)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 101 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4584)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 101 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4585)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 165 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4586)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 166 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4587)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 123 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4588)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 116 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4589)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 149 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4590)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 90 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4591)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 63 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4592)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 104 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4593)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 35 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4594)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 202 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4595)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 149 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4596)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 3 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4597)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 47 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4598)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 104 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4599)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 35 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4600)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 202 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4601)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 202 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4602)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 177 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4603)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 29 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4604)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 29 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4605)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 109 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4606)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 199 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4607)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (4480 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 4480 ≤ id.val) (hhigh : id.val < 4608) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 4480)) = true := by
  let j : Fin 128 := ⟨id.val - 4480, by omega⟩
  have hsum : 4480 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (4480 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard035
