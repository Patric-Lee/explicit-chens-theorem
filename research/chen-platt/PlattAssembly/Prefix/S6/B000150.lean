import PlattAssemblyKernel
import PlattCertificates.Count131072.C054800
import PlattCertificates.Count131072.C054801
import PlattCertificates.Count131072.C054802
import PlattCertificates.Count131072.C054803
import PlattCertificates.Count131072.C054804
import PlattCertificates.Count131072.C054805
import PlattCertificates.Count131072.C054806
import PlattCertificates.Count131072.C054807
import PlattCertificates.Count131072.C054808
import PlattCertificates.Count131072.C054809
import PlattCertificates.Count131072.C054810
import PlattCertificates.Count131072.C054811
import PlattCertificates.Count131072.C054812
import PlattCertificates.Count131072.C054813
import PlattCertificates.Count131072.C054814
import PlattCertificates.Count131072.C054815
import PlattCertificates.Count131072.C054816
import PlattCertificates.Count131072.C054817
import PlattCertificates.Count131072.C054818
import PlattCertificates.Count131072.C054819
import PlattCertificates.Count131072.C054820
import PlattCertificates.Count131072.C054821
import PlattCertificates.Count131072.C054822
import PlattCertificates.Count131072.C054823
import PlattCertificates.Count131072.C054824
import PlattCertificates.Count131072.C054825
import PlattCertificates.Count131072.C054826
import PlattCertificates.Count131072.C054827
import PlattCertificates.Count131072.C054828
import PlattCertificates.Count131072.C054829
import PlattCertificates.Count131072.C054830
import PlattCertificates.Count131072.C054831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54800 : List PrefixCut := [⟨63,222148730,222148855⟩,
⟨64,225673625,225673752⟩]
theorem checked54800 : checkPrefixCuts (2^48) 7186677761 10 Manual.Count131072.C054800.packed 64 cuts54800 = true := by
 decide +kernel
def pointBounds54800 : List (Nat × Nat × Nat) := [(7186806784,112795581493534,112795969262638)]
theorem point_links_checked54800 : (cuts54800.take 1).map (fun c => (7186677761-1+2*2^10*c.k,112795359344804+c.lower,112795747113783+c.upper)) = pointBounds54800 := by
 decide +kernel
def cuts54801 : List PrefixCut := [⟨64,227314446,227314575⟩]
theorem checked54801 : checkPrefixCuts (2^48) 7186808833 10 Manual.Count131072.C054801.packed 64 cuts54801 = true := by
 decide +kernel
def cuts54802 : List PrefixCut := [⟨45,159047130,159047219⟩,
⟨64,228446036,228446164⟩]
theorem checked54802 : checkPrefixCuts (2^48) 7186939905 10 Manual.Count131072.C054802.packed 64 cuts54802 = true := by
 decide +kernel
def pointBounds54802 : List (Nat × Nat × Nat) := [(7187032064,112795971380005,112796359149329)]
theorem point_links_checked54802 : (cuts54802.take 1).map (fun c => (7186939905-1+2*2^10*c.k,112795812332875+c.lower,112796200102110+c.upper)) = pointBounds54802 := by
 decide +kernel
def cuts54803 : List PrefixCut := [⟨64,226718685,226718810⟩]
theorem checked54803 : checkPrefixCuts (2^48) 7187070977 10 Manual.Count131072.C054803.packed 64 cuts54803 = true := by
 decide +kernel
def cuts54804 : List PrefixCut := [⟨27,95988998,95989054⟩,
⟨64,226910374,226910503⟩]
theorem checked54804 : checkPrefixCuts (2^48) 7187202049 10 Manual.Count131072.C054804.packed 64 cuts54804 = true := by
 decide +kernel
def pointBounds54804 : List (Nat × Nat × Nat) := [(7187257344,112796363486594,112796751256138)]
theorem point_links_checked54804 : (cuts54804.take 1).map (fun c => (7187202049-1+2*2^10*c.k,112796267497596+c.lower,112796655267084+c.upper)) = pointBounds54804 := by
 decide +kernel
def cuts54805 : List PrefixCut := [⟨64,226788751,226788881⟩]
theorem checked54805 : checkPrefixCuts (2^48) 7187333121 10 Manual.Count131072.C054805.packed 64 cuts54805 = true := by
 decide +kernel
def cuts54806 : List PrefixCut := [⟨9,31446983,31447001⟩,
⟨64,226510474,226510601⟩]
theorem checked54806 : checkPrefixCuts (2^48) 7187464193 10 Manual.Count131072.C054806.packed 64 cuts54806 = true := by
 decide +kernel
def pointBounds54806 : List (Nat × Nat × Nat) := [(7187482624,112796752643704,112797140413469)]
theorem point_links_checked54806 : (cuts54806.take 1).map (fun c => (7187464193-1+2*2^10*c.k,112796721196721+c.lower,112797108966468+c.upper)) = pointBounds54806 := by
 decide +kernel
def cuts54807 : List PrefixCut := [⟨55,193493981,193494091⟩,
⟨64,223843402,223843530⟩]
theorem checked54807 : checkPrefixCuts (2^48) 7187595265 10 Manual.Count131072.C054807.packed 64 cuts54807 = true := by
 decide +kernel
def pointBounds54807 : List (Nat × Nat × Nat) := [(7187707904,112797141201176,112797528971160)]
theorem point_links_checked54807 : (cuts54807.take 1).map (fun c => (7187595265-1+2*2^10*c.k,112796947707195+c.lower,112797335477069+c.upper)) = pointBounds54807 := by
 decide +kernel
def cuts54808 : List PrefixCut := [⟨64,227442059,227442191⟩]
theorem checked54808 : checkPrefixCuts (2^48) 7187726337 10 Manual.Count131072.C054808.packed 64 cuts54808 = true := by
 decide +kernel
def cuts54809 : List PrefixCut := [⟨37,129735654,129735728⟩,
⟨64,226145641,226145770⟩]
theorem checked54809 : checkPrefixCuts (2^48) 7187857409 10 Manual.Count131072.C054809.packed 64 cuts54809 = true := by
 decide +kernel
def pointBounds54809 : List (Nat × Nat × Nat) := [(7187933184,112797528728310,112797916498518)]
theorem point_links_checked54809 : (cuts54809.take 1).map (fun c => (7187857409-1+2*2^10*c.k,112797398992656+c.lower,112797786762790+c.upper)) = pointBounds54809 := by
 decide +kernel
def cuts54810 : List PrefixCut := [⟨64,222734719,222734846⟩]
theorem checked54810 : checkPrefixCuts (2^48) 7187988481 10 Manual.Count131072.C054810.packed 64 cuts54810 = true := by
 decide +kernel
def cuts54811 : List PrefixCut := [⟨19,67156386,67156424⟩,
⟨64,224649401,224649527⟩]
theorem checked54811 : checkPrefixCuts (2^48) 7188119553 10 Manual.Count131072.C054811.packed 64 cuts54811 = true := by
 decide +kernel
def pointBounds54811 : List (Nat × Nat × Nat) := [(7188158464,112797915029402,112798302799830)]
theorem point_links_checked54811 : (cuts54811.take 1).map (fun c => (7188119553-1+2*2^10*c.k,112797847873016+c.lower,112798235643406+c.upper)) = pointBounds54811 := by
 decide +kernel
def cuts54812 : List PrefixCut := [⟨64,225154365,225154493⟩]
theorem checked54812 : checkPrefixCuts (2^48) 7188250625 10 Manual.Count131072.C054812.packed 64 cuts54812 = true := by
 decide +kernel
def cuts54813 : List PrefixCut := [⟨1,3641593,3641595⟩,
⟨64,225150257,225150387⟩]
theorem checked54813 : checkPrefixCuts (2^48) 7188381697 10 Manual.Count131072.C054813.packed 64 cuts54813 = true := by
 decide +kernel
def pointBounds54813 : List (Nat × Nat × Nat) := [(7188383744,112798301318375,112798689089021)]
theorem point_links_checked54813 : (cuts54813.take 1).map (fun c => (7188381697-1+2*2^10*c.k,112798297676782+c.lower,112798685447426+c.upper)) = pointBounds54813 := by
 decide +kernel
def cuts54814 : List PrefixCut := [⟨47,165512196,165512291⟩,
⟨64,225341931,225342059⟩]
theorem checked54814 : checkPrefixCuts (2^48) 7188512769 10 Manual.Count131072.C054814.packed 64 cuts54814 = true := by
 decide +kernel
def pointBounds54814 : List (Nat × Nat × Nat) := [(7188609024,112798688339235,112799076110104)]
theorem point_links_checked54814 : (cuts54814.take 1).map (fun c => (7188512769-1+2*2^10*c.k,112798522827039+c.lower,112798910597813+c.upper)) = pointBounds54814 := by
 decide +kernel
def cuts54815 : List PrefixCut := [⟨64,223889081,223889207⟩]
theorem checked54815 : checkPrefixCuts (2^48) 7188643841 10 Manual.Count131072.C054815.packed 64 cuts54815 = true := by
 decide +kernel
def cuts54816 : List PrefixCut := [⟨29,101332151,101332208⟩,
⟨64,226312544,226312671⟩]
theorem checked54816 : checkPrefixCuts (2^48) 7188774913 10 Manual.Count131072.C054816.packed 64 cuts54816 = true := by
 decide +kernel
def pointBounds54816 : List (Nat × Nat × Nat) := [(7188834304,112799073390202,112799461161287)]
theorem point_links_checked54816 : (cuts54816.take 1).map (fun c => (7188774913-1+2*2^10*c.k,112798972058051+c.lower,112799359829079+c.upper)) = pointBounds54816 := by
 decide +kernel
def cuts54817 : List PrefixCut := [⟨64,228109523,228109651⟩]
theorem checked54817 : checkPrefixCuts (2^48) 7188905985 10 Manual.Count131072.C054817.packed 64 cuts54817 = true := by
 decide +kernel
def cuts54818 : List PrefixCut := [⟨11,39505670,39505693⟩,
⟨64,227439751,227439880⟩]
theorem checked54818 : checkPrefixCuts (2^48) 7189037057 10 Manual.Count131072.C054818.packed 64 cuts54818 = true := by
 decide +kernel
def pointBounds54818 : List (Nat × Nat × Nat) := [(7189059584,112799465985788,112799853757094)]
theorem point_links_checked54818 : (cuts54818.take 1).map (fun c => (7189037057-1+2*2^10*c.k,112799426480118+c.lower,112799814251401+c.upper)) = pointBounds54818 := by
 decide +kernel
def cuts54819 : List PrefixCut := [⟨57,205353907,205354022⟩,
⟨64,231468267,231468397⟩]
theorem checked54819 : checkPrefixCuts (2^48) 7189168129 10 Manual.Count131072.C054819.packed 64 cuts54819 = true := by
 decide +kernel
def pointBounds54819 : List (Nat × Nat × Nat) := [(7189284864,112799859273776,112800247045303)]
theorem point_links_checked54819 : (cuts54819.take 1).map (fun c => (7189168129-1+2*2^10*c.k,112799653919869+c.lower,112800041691281+c.upper)) = pointBounds54819 := by
 decide +kernel
def cuts54820 : List PrefixCut := [⟨64,226335186,226335313⟩]
theorem checked54820 : checkPrefixCuts (2^48) 7189299201 10 Manual.Count131072.C054820.packed 64 cuts54820 = true := by
 decide +kernel
def cuts54821 : List PrefixCut := [⟨39,138868565,138868644⟩,
⟨64,225939581,225939709⟩]
theorem checked54821 : checkPrefixCuts (2^48) 7189430273 10 Manual.Count131072.C054821.packed 64 cuts54821 = true := by
 decide +kernel
def pointBounds54821 : List (Nat × Nat × Nat) := [(7189510144,112800250591887,112800638363635)]
theorem point_links_checked54821 : (cuts54821.take 1).map (fun c => (7189430273-1+2*2^10*c.k,112800111723322+c.lower,112800499494991+c.upper)) = pointBounds54821 := by
 decide +kernel
def cuts54822 : List PrefixCut := [⟨64,224565186,224565312⟩]
theorem checked54822 : checkPrefixCuts (2^48) 7189561345 10 Manual.Count131072.C054822.packed 64 cuts54822 = true := by
 decide +kernel
def cuts54823 : List PrefixCut := [⟨21,75363107,75363150⟩,
⟨64,227732220,227732348⟩]
theorem checked54823 : checkPrefixCuts (2^48) 7189692417 10 Manual.Count131072.C054823.packed 64 cuts54823 = true := by
 decide +kernel
def pointBounds54823 : List (Nat × Nat × Nat) := [(7189735424,112800637591196,112801025363162)]
theorem point_links_checked54823 : (cuts54823.take 1).map (fun c => (7189692417-1+2*2^10*c.k,112800562228089+c.lower,112800950000012+c.upper)) = pointBounds54823 := by
 decide +kernel
def cuts54824 : List PrefixCut := [⟨64,226318700,226318828⟩]
theorem checked54824 : checkPrefixCuts (2^48) 7189823489 10 Manual.Count131072.C054824.packed 64 cuts54824 = true := by
 decide +kernel
def cuts54825 : List PrefixCut := [⟨3,9982826,9982832⟩,
⟨64,225727338,225727467⟩]
theorem checked54825 : checkPrefixCuts (2^48) 7189954561 10 Manual.Count131072.C054825.packed 64 cuts54825 = true := by
 decide +kernel
def pointBounds54825 : List (Nat × Nat × Nat) := [(7189960704,112801026261835,112801414034020)]
theorem point_links_checked54825 : (cuts54825.take 1).map (fun c => (7189954561-1+2*2^10*c.k,112801016279009+c.lower,112801404051188+c.upper)) = pointBounds54825 := by
 decide +kernel
def cuts54826 : List PrefixCut := [⟨49,172130988,172131087⟩,
⟨64,225644954,225645082⟩]
theorem checked54826 : checkPrefixCuts (2^48) 7190085633 10 Manual.Count131072.C054826.packed 64 cuts54826 = true := by
 decide +kernel
def pointBounds54826 : List (Nat × Nat × Nat) := [(7190185984,112801414137335,112801801909742)]
theorem point_links_checked54826 : (cuts54826.take 1).map (fun c => (7190085633-1+2*2^10*c.k,112801242006347+c.lower,112801629778655+c.upper)) = pointBounds54826 := by
 decide +kernel
def cuts54827 : List PrefixCut := [⟨64,229320609,229320735⟩]
theorem checked54827 : checkPrefixCuts (2^48) 7190216705 10 Manual.Count131072.C054827.packed 64 cuts54827 = true := by
 decide +kernel
def cuts54828 : List PrefixCut := [⟨31,111644513,111644576⟩,
⟨64,225910767,225910897⟩]
theorem checked54828 : checkPrefixCuts (2^48) 7190347777 10 Manual.Count131072.C054828.packed 64 cuts54828 = true := by
 decide +kernel
def pointBounds54828 : List (Nat × Nat × Nat) := [(7190411264,112801808616423,112802196389048)]
theorem point_links_checked54828 : (cuts54828.take 1).map (fun c => (7190347777-1+2*2^10*c.k,112801696971910+c.lower,112802084744472+c.upper)) = pointBounds54828 := by
 decide +kernel
def cuts54829 : List PrefixCut := [⟨64,226532950,226533078⟩]
theorem checked54829 : checkPrefixCuts (2^48) 7190478849 10 Manual.Count131072.C054829.packed 64 cuts54829 = true := by
 decide +kernel
def cuts54830 : List PrefixCut := [⟨13,44938134,44938160⟩,
⟨64,223514702,223514832⟩]
theorem checked54830 : checkPrefixCuts (2^48) 7190609921 10 Manual.Count131072.C054830.packed 64 cuts54830 = true := by
 decide +kernel
def pointBounds54830 : List (Nat × Nat × Nat) := [(7190636544,112802194353761,112802582126607)]
theorem point_links_checked54830 : (cuts54830.take 1).map (fun c => (7190609921-1+2*2^10*c.k,112802149415627+c.lower,112802537188447+c.upper)) = pointBounds54830 := by
 decide +kernel
def cuts54831 : List PrefixCut := [⟨59,206639832,206639949⟩,
⟨64,224176069,224176196⟩]
theorem checked54831 : checkPrefixCuts (2^48) 7190740993 10 Manual.Count131072.C054831.packed 64 cuts54831 = true := by
 decide +kernel
def pointBounds54831 : List (Nat × Nat × Nat) := [(7190861824,112802579570161,112802967343228)]
theorem point_links_checked54831 : (cuts54831.take 1).map (fun c => (7190740993-1+2*2^10*c.k,112802372930329+c.lower,112802760703279+c.upper)) = pointBounds54831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000150
