import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard015
open N4R2RowDataReplay

-- Original cycle 0b34220e671689e8b4ad4d524ee4f62c27a5b29bc6abc704892fd51fdcbd99b3; original global index 895.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1053ac9beed819abfcca8fae1f4da2b28fe1185b1b3990b75e4e740496255005; original global index 1314.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 1094a470bac7414e3104c75783c5aecaf7d8ca6e7849754986c0d777f98a925b; original global index 1329.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0]

-- Original cycle 17a0e0ad45fa34a6a54dcbb4c6495220a4c54e23a55adcfc6c7f984df2cb43bd; original global index 1847.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 18234cb3f60f072a660b0a813a200983f9a84534a43de4eba30550be7334b240; original global index 1889.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1b28dff94edba3354fd308506f9f0d275cf882869fb3214b2db16173148e02e4; original global index 2103.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 230e8b6887e0e9fbf420ca5ac5233c4776a935ff1a3cc9ce19bed785f8ac7092; original global index 2688.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 241eb5b62fed0e9e3bed4c1517d40c928f4bc0ec92d5ba3c8a3421d80d54db9d; original global index 2767.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Original cycle 25943ff23356a2fdfa8b70df3d31bdf5b4c3ec79b5b335136d33f97e07e5e907; original global index 2888.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 27c34ae7e020cc6b762339a8ff1c2a0789efe134c8b75944ed951ec6b05b08c6; original global index 3038.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00010 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2ab0667010f87ac469da178fd116ceeea8ffaca27230a02ef22c44c99b1636cc; original global index 3245.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2af08d5770eaf2d8ec0458d5aa668a1ea83cbfb96accad29ae8abd72be967a7d; original global index 3274.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2b6f485331a0dcc6084b40a09a41f06350a38c9b755b67ec25cc7bdee98681e3; original global index 3322.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 2cee7677487af76de854f378eefd594aea12674ed5e3f077daf29c3bdf3c0ef4; original global index 3430.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 30b92d10747753e98b9811e218841e4f7b73c9ae0664349d2d6249c429ab6fe0; original global index 3715.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 30c74e5bd7c02d8fe3f832692c5997689fcdebbc515b535d6a401260d1e9fe20; original global index 3721.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 32896f25ba7f0401014ee25c4fd2ec5a3b1eb2650bb3628991f8649da5622b49; original global index 3865.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 335b4fec4717c48a13f406f64b88f3e11058dc38fa7dc1cc192c8b237160ab47; original global index 3931.
def localCycle00018 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 35e64640f9dcd4d2556f61ae44bf2c16db791631bdb695cc2cbcf90c5be745cf; original global index 4135.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3745a6088e3e87fc3a665dd651fbc43fbb6cb4d653569eb33226b0c29b4ada1b; original global index 4245.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 399183be39d113a17b3a05eab3a841a17c5bc4cdda4ed3b2cce0d9718629ce99; original global index 4436.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3a0ddd6f89c1aa9f2c34b3b1df20752346eaf2218663cefe01bcb2945aa449d8; original global index 4478.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3b5f33304db84e2c7b4facf0b37f23fd6a5f94523e6967221e2b7aace24b6acd; original global index 4590.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3c20fa31453edf9a44371e48ae30f3cca538002e6179f976f8b53c4aa99ddf88; original global index 4661.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3d4b1120274a2630565f6b9e7861c2333a5d8be69400e96b476f947924925b67; original global index 4748.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 4007896e30b41ad49a517bb29a7fa85a377aea067678275aded96f686d5f9d62; original global index 4938.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 40b72c9473514f79a209af7b9706d8e246c477082a4b92c4f6f12cec5e01db6d; original global index 5000.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 420f195e0a9b6b44e93cfe41107cca5f585d9449deabff56e76f87926d98a59e; original global index 5090.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 423e20f28018b9d4506d0799d62e570b0c2ec6ee8be36c68321cff675fc394f3; original global index 5102.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 42e57fe5a431b2a503a44f28ce592d5042bb19dacc4efd972c8fd3227d6ba9ca; original global index 5151.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 43486cf93b55c9406774eb7ec3ab3b1b4d6ce99149661e7d140a87d6f53884ec; original global index 5194.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 4ac75c3163008ddda27e54fd0b0a5af9b600866756b3446a66fb8cc3b6e0caeb; original global index 5800.
def localCycle00033 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 3, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4b430bf94413a929d64699658ada4e0fd0f0bcf528ff30ef9ddf01c5ad8c81c8; original global index 5835.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 4c0270feee30cc7460db583ed51ba1463eaa710a401234b57a5d4d69b68aee7b; original global index 5899.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 4c47c8822de48797e04b6e81155be1c9e6b318a7bebf56f64f28d4c9514fcfc7; original global index 5920.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 4eee0be7ac7f8c05ae7fca78fbac71755a287726f2781b321eefd6f9a6e814df; original global index 6133.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 51260c85946f28b9d88479db4c5ac577822a9b10b0024b8e908eb65b567d8fae; original global index 6305.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 524fb6adb910d12cbf7d9e060ec118ac6794476ca4d6200a5287620b9554e747; original global index 6398.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00040 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 58e51f9a6c19c7adefb51092b7ade5a1b5f1f9f77bca590e68870ad20c664c26; original global index 6896.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 5a218a4d7680063e773bdb17458053a7d1356f8f3ce394d06a2e3ad136dc1dfc; original global index 7015.
def localCycle00042 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 5f1339bcef79781d7b64904198c61b95c2a2abc7b31a4b66ea99472ea4bb81b6; original global index 7405.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 6198266c3a0bd4a34e5323da63bc12deabb8e3822b517778d27835dd72a2affa; original global index 7615.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 61f3fa97f2cfc25f3bb5ec4c364c50a2ca9378a6303b59542690e3f1d5787c04; original global index 7648.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 63345926e582c286eaada871ae829986f0a86a5d9d4fc9530e6c66c9434488ef; original global index 7738.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 66ad46e74633233b123c2154f90d9129861544c2471a675c685c423ddeb050d5; original global index 7981.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00048 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6a73489313912e5420017d1ccb9d9ec83b819972e0f36427beca5b2e1544c2ec; original global index 8289.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 6d183bf24f4944910511cdd02a739bf775b9c695f202bf951b1fc23f3ce9227d; original global index 8484.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .gapLower 6 0, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6f7d959349c6f95dc72f0b1f7619678e73704b2a274a9acb621585e0213fbea4; original global index 8647.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 72c34dfe2d5af3732e917553b50c36b9a6e43ce2262ff3254e539410047e35fd; original global index 8886.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 73587ad851e1c21682a2d763595ac0e10630b8b9d793fbc7c14f6439ad3cbcc3; original global index 8931.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 7db0b8f5390418c2497f6c1d544b0dfe94eb412bdc34f7a145276f5e2065aa57; original global index 9755.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 7e700f18a15088f4c77c5fad4e2831a5c99df6e4a01184ead22b78c6c7aef532; original global index 9821.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 7fc76e027800ff195bfa07ea80d28586e2a37906df55d35f6b6cfec0e9fd5f03; original global index 9911.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 3, .triangle 17 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 80784293f397a8189530bc3fc41f26bcb13248f4ffb318c2c93158cafac631f4; original global index 9970.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 8486744b86d69cee65a680d626f68fc2576e8536eaae24178dd22df69556e939; original global index 10290.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 886d04b1acc0b8039cbf8f874b3cb295c3a916cae978c35688d369e5d36986c5; original global index 10570.
def localCycle00059 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0]

-- Original cycle 8f5840d349f7310e7c101dec7a3ce48016c7531cb246b92cd98d98f81dca890b; original global index 11094.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 92ce83c9da10931539fab072f921e861b4de0fc9c4b2e30d22e39d4895c380de; original global index 11377.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 92e61a258b5a1303a1c9893ae8c211772c5e98c07cce3e39470929f33a3c0c4c; original global index 11388.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 9402900322bbc6536aeac733f4f03495a888f641f3001ba5896cc3a315ab23c4; original global index 11479.
def localCycle00063 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle 9498820c22d8d3c8e6db069324470c3d4be83f7fd73f88ce1a1675d82d9e8f7e; original global index 11530.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 94fdd5388973248006ad48ad20fb3f97c031a72368105aafbfbc41735838d469; original global index 11565.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 973d196ce4cae0a238a7de1adb2afc18b1ef9ccd73e3397cca54f5f7e5038c5b; original global index 11752.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 98cafdb643cbc332d5a47545e007008ef0e0b34de8ba76200b245140c001ae06; original global index 11866.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 995e5ad6f431cca36439fe164e5ca53445b5caac85154f8420cfa81e9ff18220; original global index 11908.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 99f4d6b13c1c5c464270d5808d97f6b2fbc2bf7bc2dcdaff478ecef7b3e4c434; original global index 11953.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9bc2b559f34353e8adb0fd3ff7f3d98946a52176967c6f1f4add54e26dd98cc1; original global index 12119.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle 9e3567b6ca609c077b5abe332844bbac5d1708e2d7b8ba7b094af3005718fbd6; original global index 12316.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 9f4edb352f77dd77b7ae3af210a2eb2e79ed3c6919af2c9ab194ee5db98c10ec; original global index 12400.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a053f2d5b6c282a8ff8986d1179f96779d887c8c2b5a5a086d04810072e9a40f; original global index 12476.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a113a9408c8f5b4c870eb700d7a8af131f33532f9819da34f87f5fd03d004389; original global index 12526.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle a333779d6959f2156b306217eabb83f9bdd2d318912ff6e1cbbcda14776f01c9; original global index 12686.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a3c561136fee1df73a2145d1128263874b2c1b3b53aa038f1a1f0f4600034b60; original global index 12735.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a44981bccf878c8a259a6c0f66871d73585d2793ba20bbbe93f9a6174464db2b; original global index 12768.
def localCycle00077 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle a4e4264001169ef20f0e04d48fcc1f8ff86b65fbcdce7ae01b3a287ed860fe53; original global index 12815.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 2, .gapUpper 3 2]

-- Original cycle a571e62a5d5c8cfc2b9eced04425ca3b34f27adaded25a181d0f75c7d2cd8156; original global index 12855.
def localCycle00079 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 26 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0]

-- Original cycle a761f6d7e0662ccc5d19c332394b913137771b521da4ce5649db9a88b682e941; original global index 13022.
def localCycle00080 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle aa1913b317ac6d7198c5f2cd447c8e394067bcaa8bbb3bb440236abbaea50cc6; original global index 13243.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ada9a3f8d0a4a41f1e9da21295c7df4becd3f7b75c32ab721c50418eebd6bec9; original global index 13555.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle adcb3ad571cc75af60d442f7e2ffb246800032b342766a9524463a833cb6635b; original global index 13563.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle add6792330f04b3debf01024e8dafedc61264691bdc7586e7af942f0236a4859; original global index 13564.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle af80b9228b17629cab283e0a4c1c8195569772000a2034e95203dd226ffd6e52; original global index 13705.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle b021ad4ff761e54acf0036e2ed7f8d25236c2f7696e46924cd468915ffa2265c; original global index 13752.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b15e4c5d721afc9ab8d6313f88ecf7d1f38c5f10e933ee8f319aeb9854ff610f; original global index 13856.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b2ce812deb97f66615cd4157dae5a6044b5e7c7a4c643ad775c486f9f9d805ca; original global index 13977.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle b8168c5549051cc4d62dcc3073b391dcdc4da49a127c1ba85b74548a3144b8ca; original global index 14361.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b8532a1d7bc6e00015ff2ebac6487acfe391ff6868976b2924cf5848655a5b99; original global index 14382.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b8e17c13012af53a3d41c0742ae6b8d63edba942ffad97dbafde00685385e2df; original global index 14432.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle bbcb6df18184052ade0ffeeadca621161936fe18a5a433f79589380a6f780103; original global index 14667.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .corridorLower 3 5]

-- Original cycle bce286f1392effab3cd1493fc0d1b54a53966871684a2c77d8497f8ebd5f228f; original global index 14735.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bd11da19a322d66411d2336a57e58c875abd98e65d1476aa4af0d722817f1aea; original global index 14751.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle c22c34a2d0053577f0cedf424a853c909fcd57076f870011ed647f5a23a591b8; original global index 15162.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c3de3aadf3c72b35ada4dd2665581bbf46c4d05cf0498bf2e9c79f0fd6267766; original global index 15279.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 4, .gapLower 3 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle c5283decb53b0a63efc12cb9e99130aa8d1910fcd1ad8515c61b5c385865932b; original global index 15381.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c5f8919fee4f4a92f2f1e580459424cb0f3c4e38bf13c9bf2ed8322f99945b2e; original global index 15440.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle c700228370a85c2cf658991dbaa09533bc9ff4bae370bf86700728c78c7d6758; original global index 15529.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle ca97ea4e8d89567002bc96674ee5db7c20d0ada011fa6655cadfd58e32f94d14; original global index 15838.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 21 2, .gapLower 6 3, .triangle 11 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle cb4fb0bfc87a29b1caed1085298f2c5b32bd3b75646dca271147584a724b1ac7; original global index 15881.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle cec5d8999d15dec2fa5dcaf82c7311f9703513ddd08a2c19fe24a4a7d5abe577; original global index 16139.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle d0ad4675fee1587e74318fced5784a394bf78538730b70d7a4fbf27c57ca0b45; original global index 16284.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .gapLower 3 2, .triangle 10 0, .corridorLower 3 5]

-- Original cycle d1b13e1b64db1b8394324bcfb3ee7c2a81721b7e09dc93c361bb8b2b95a34882; original global index 16367.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d36a18f1258badcbc355c5e6d4dae8c3045eb26606aa5aa01862856792aebdd0; original global index 16491.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d3764a629be4ba4046d82003979ca476ac2e33e9403bedc07845e6a67abd6e68; original global index 16497.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 11 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d4fbecf6e40f956673ab7d9c69c82c167300b9b7240f92b89e3f1843bf33a945; original global index 16616.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle d5cfd9f8f6c6075e5b60d3e9e2bec8cd51a143278ab86c5109ec000d64af820c; original global index 16689.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle d7d0ebf003ebd8bbf7c9d1df3a192fe3f122502e8e634635e3320b9f47dd30cd; original global index 16840.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle da5eb68bb63ef4e9c66c770d7ae7070b4044de184625e1ba0e3beb8e3a767fae; original global index 17064.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e1454bde9f681d18d54e363c51185edda3b06745487f9470d10176142eca14a4; original global index 17617.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e2c2dc82005be310c7666793eb02945af3efda547b7e95110dd6c40afa29d91d; original global index 17734.
def localCycle00113 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 27 0]

-- Original cycle e3c5842bc536ab252f6e2b422ba904ddda9a29d4a3eac75732c392ce04fef702; original global index 17820.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle e73ec6227d548b31447db5132c288676a7f60cc33cbf614707161a2318e0cb03; original global index 18088.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle e743b5d74cd80a53a91d62e047310312b99c5b5954d365ff07f92fbd3ef6cb56; original global index 18090.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e95a42df13491c913ac690dc19bb6a9086da793b1f7a8a00055f783de849e8bb; original global index 18238.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .triangle 32 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ed203cb8589e1a1de944b8cd44ec43518a0dae0f15fbaf378846f6a4ac22df18; original global index 18513.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle ed37fd5ef4197f05d85dcf7d734f4b39aeb56f6862722dcdf8c0966e0e6a9ddb; original global index 18522.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle eec54fbf9cd69d2562e0a6e671b2f2a9fb46a287c296ab4f759dbb516dd6a389; original global index 18635.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle f2047655e3807a8fec0bb2881f1f01bd4bb2eab7e9d8411f2717450da7fd8258; original global index 18872.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f238ccef9174cff88e10374cb4a92b979042ff9a486a48f714489ea346eff147; original global index 18892.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle f464216711a39b6737af18801dd7b4fa1889bd92cbf8a67b7025215801bac6f2; original global index 19050.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .gapLower 3 2, .triangle 10 0, .corridorLower 3 5]

-- Original cycle f83774d6d7e900d5f9153076c8e574a41100da0c2fe12f62b6ae7cdadf8dffc8; original global index 19359.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f99601cde1e56ab02e4f603355494bc2fe3a413ddf29fe8ca5f5c8a8048029dd; original global index 19456.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle fd277a3a3415df86bbeca3ac2307f229922ef9184d1fb18c89cc0939c4a9bf6a; original global index 19784.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle fd96a7d7fe00d3c1cf5e72fade6712efe429a58d12f49e1f1ad684bd31af2cd7; original global index 19824.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle fe1eb5c9259369c0123c5fbd11468094bf6a80795f7c6a49e5db37dbf913b3dd; original global index 19860.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Original cycle ffb23e3354dea30dea6c32502b58667870084f817723979b99ba4bb3ab924d2d; original global index 19996.
def localCycle00129 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

def library : Library := fun id => if id < 65 then (if id < 32 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))))) else (if id < 48 then (if id < 40 then (if id < 36 then (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)))) else (if id < 44 then (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 56 then (if id < 52 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))))))) else (if id < 97 then (if id < 81 then (if id < 73 then (if id < 69 then (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 77 then (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))))) else (if id < 89 then (if id < 85 then (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 93 then (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))) else (if id < 113 then (if id < 105 then (if id < 101 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 109 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))))) else (if id < 121 then (if id < 117 then (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))) else (if id < 125 then (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 6, 3, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![6, 0, 5, 2, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 102 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1920)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 6, 3, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 0, 5, 4, 2, 1], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 36 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1921)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1922)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 72 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1923)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 71 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1924)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 76 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1925)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 111 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1926)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 15 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1927)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 49 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1928)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 9 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1929)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 124 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1930)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 124 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1931)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 67 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1932)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 82 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1933)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![21, 10, 30, 75, 23, 63, 5, 26, 118, 66, 48, 113, 65, 116, 47, 18, 113, 65, 110, 20, 113, 96, 37, 113, 81, 77, 86, 113]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1934)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 15 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1935)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 124 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1936)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 49 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1937)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 124 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1938)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 67 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1939)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 82 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1940)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low6 (![31, 25, 78, 107, 28, 92, 5, 80, 8, 46, 117, 33, 50, 129, 101, 34, 100, 87, 51, 90, 60, 61, 74, 39, 61, 38, 52, 3]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1941)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 73 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1942)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 85 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1943)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 69 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1944)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 40 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1945)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 89 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1946)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 94 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1947)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![5, 6, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 94 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1948)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 40 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1949)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![6, 5, 0, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 27 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1950)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 108 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1951)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 4 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1952)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 95 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1953)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 64 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1954)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 64 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1955)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 44 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1956)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 120 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1957)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 4, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 64 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1958)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 64 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1959)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 44 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1960)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 84 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1961)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 84 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1962)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 83 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1963)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 3, 6, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 43 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1964)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 68 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1965)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 68 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1966)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 84 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1967)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 84 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1968)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 5, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 24 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1969)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 24 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1970)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 16 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1971)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 106 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1972)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 19 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1973)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 126 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1974)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 16 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1975)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 106 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1976)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 19 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1977)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 126 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1978)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1979)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 32 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1980)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 114 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1981)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 127 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1982)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 95 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1983)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 14 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1984)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 91 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1985)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 3, 6], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 13 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1986)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 120 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1987)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 120 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1988)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 91 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1989)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 99 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1990)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 91 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1991)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 122 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1992)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 62 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1993)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 6 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1994)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 29 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1995)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 88 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1996)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 3, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 2, 1]], proof := .tail 62 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1997)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 98 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1998)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 98 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1999)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 98 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2000)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 54 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2001)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 0 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2002)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 12 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2003)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 6, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 2, 1]], proof := .tail 105 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2004)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 2, 1]], proof := .tail 54 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2005)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 2, 1]], proof := .tail 0 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2006)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 6, 5, 3, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 2, 1]], proof := .tail 12 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2007)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![5, 0, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 59 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2008)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 55 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2009)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 35 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2010)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 97 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2011)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2012)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2013)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 95 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2014)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 104 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2015)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![5, 0, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 17 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2016)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 15 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2017)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 64 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2018)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 49 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2019)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 44 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2020)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2021)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 32 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2022)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 114 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2023)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 11 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2024)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 95 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2025)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 14 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2026)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 91 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2027)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![5, 0, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 1 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2028)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 44 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2029)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 103 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2030)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 121 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2031)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 42 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2032)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 70 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2033)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 53 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2034)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 22 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2035)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 128 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2036)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 123 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2037)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 93 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2038)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![5, 0, 2, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 109 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2039)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![5, 0, 2, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 112 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2040)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 6, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 45 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2041)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 125 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2042)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 57 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2043)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![5, 0, 2, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 41 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2044)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![5, 0, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 3, 0, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 119 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2045)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![5, 0, 2, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2046)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 5, 3, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![5, 0, 2, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 58 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2047)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1920 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1920 ≤ id.val) (hhigh : id.val < 2048) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1920)) = true := by
  let j : Fin 128 := ⟨id.val - 1920, by omega⟩
  have hsum : 1920 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1920 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard015
