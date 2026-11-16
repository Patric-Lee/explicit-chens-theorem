import PlattAssemblyKernel
import PlattCertificates.Count131072.C060096
import PlattCertificates.Count131072.C060097
import PlattCertificates.Count131072.C060098
import PlattCertificates.Count131072.C060099
import PlattCertificates.Count131072.C060100
import PlattCertificates.Count131072.C060101
import PlattCertificates.Count131072.C060102
import PlattCertificates.Count131072.C060103
import PlattCertificates.Count131072.C060104
import PlattCertificates.Count131072.C060105
import PlattCertificates.Count131072.C060106
import PlattCertificates.Count131072.C060107
import PlattCertificates.Count131072.C060108
import PlattCertificates.Count131072.C060109
import PlattCertificates.Count131072.C060110
import PlattCertificates.Count131072.C060111
import PlattCertificates.Count131072.C060112
import PlattCertificates.Count131072.C060113
import PlattCertificates.Count131072.C060114
import PlattCertificates.Count131072.C060115
import PlattCertificates.Count131072.C060116
import PlattCertificates.Count131072.C060117
import PlattCertificates.Count131072.C060118
import PlattCertificates.Count131072.C060119
import PlattCertificates.Count131072.C060120
import PlattCertificates.Count131072.C060121
import PlattCertificates.Count131072.C060122
import PlattCertificates.Count131072.C060123
import PlattCertificates.Count131072.C060124
import PlattCertificates.Count131072.C060125
import PlattCertificates.Count131072.C060126
import PlattCertificates.Count131072.C060127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60096 : List PrefixCut := [⟨64,208439049,208439168⟩]
theorem checked60096 : checkPrefixCuts (2^48) 7880835073 10 Manual.Count131072.C060096.packed 64 cuts60096 = true := by
 decide +kernel
def cuts60097 : List PrefixCut := [⟨18,56609388,56609421⟩,
⟨64,202863975,202864091⟩]
theorem checked60097 : checkPrefixCuts (2^48) 7880966145 10 Manual.Count131072.C060097.packed 64 cuts60097 = true := by
 decide +kernel
def pointBounds60097 : List (Nat × Nat × Nat) := [(7881003008,113936780501503,113937168920120)]
theorem point_links_checked60097 : (cuts60097.take 1).map (fun c => (7880966145-1+2*2^10*c.k,113936723892115+c.lower,113937112310699+c.upper)) = pointBounds60097 := by
 decide +kernel
def cuts60098 : List PrefixCut := [⟨64,208789276,208789388⟩]
theorem checked60098 : checkPrefixCuts (2^48) 7881097217 10 Manual.Count131072.C060098.packed 64 cuts60098 = true := by
 decide +kernel
def cuts60099 : List PrefixCut := [⟨11,36000263,36000284⟩,
⟨64,204142945,204143064⟩]
theorem checked60099 : checkPrefixCuts (2^48) 7881228289 10 Manual.Count131072.C060099.packed 64 cuts60099 = true := by
 decide +kernel
def pointBounds60099 : List (Nat × Nat × Nat) := [(7881250816,113937171545629,113937559964462)]
theorem point_links_checked60099 : (cuts60099.take 1).map (fun c => (7881228289-1+2*2^10*c.k,113937135545366+c.lower,113937523964178+c.upper)) = pointBounds60099 := by
 decide +kernel
def cuts60100 : List PrefixCut := [⟨64,207496644,207496762⟩]
theorem checked60100 : checkPrefixCuts (2^48) 7881359361 10 Manual.Count131072.C060100.packed 64 cuts60100 = true := by
 decide +kernel
def cuts60101 : List PrefixCut := [⟨4,12999674,12999682⟩,
⟨64,204314724,204314844⟩]
theorem checked60101 : checkPrefixCuts (2^48) 7881490433 10 Manual.Count131072.C060101.packed 64 cuts60101 = true := by
 decide +kernel
def pointBounds60101 : List (Nat × Nat × Nat) := [(7881498624,113937560184629,113937948603686)]
theorem point_links_checked60101 : (cuts60101.take 1).map (fun c => (7881490433-1+2*2^10*c.k,113937547184955+c.lower,113937935604004+c.upper)) = pointBounds60101 := by
 decide +kernel
def cuts60102 : List PrefixCut := [⟨61,196561791,196561904⟩,
⟨64,206096957,206097076⟩]
theorem checked60102 : checkPrefixCuts (2^48) 7881621505 10 Manual.Count131072.C060102.packed 64 cuts60102 = true := by
 decide +kernel
def pointBounds60102 : List (Nat × Nat × Nat) := [(7881746432,113937948061470,113938336480752)]
theorem point_links_checked60102 : (cuts60102.take 1).map (fun c => (7881621505-1+2*2^10*c.k,113937751499679+c.lower,113938139918848+c.upper)) = pointBounds60102 := by
 decide +kernel
def cuts60103 : List PrefixCut := [⟨64,205486439,205486561⟩]
theorem checked60103 : checkPrefixCuts (2^48) 7881752577 10 Manual.Count131072.C060103.packed 64 cuts60103 = true := by
 decide +kernel
def cuts60104 : List PrefixCut := [⟨54,173307303,173307404⟩,
⟨64,205197296,205197416⟩]
theorem checked60104 : checkPrefixCuts (2^48) 7881883649 10 Manual.Count131072.C060104.packed 64 cuts60104 = true := by
 decide +kernel
def pointBounds60104 : List (Nat × Nat × Nat) := [(7881994240,113938336390378,113938724809889)]
theorem point_links_checked60104 : (cuts60104.take 1).map (fun c => (7881883649-1+2*2^10*c.k,113938163083075+c.lower,113938551502485+c.upper)) = pointBounds60104 := by
 decide +kernel
def cuts60105 : List PrefixCut := [⟨64,204836788,204836907⟩]
theorem checked60105 : checkPrefixCuts (2^48) 7882014721 10 Manual.Count131072.C060105.packed 64 cuts60105 = true := by
 decide +kernel
def cuts60106 : List PrefixCut := [⟨47,150732842,150732927⟩,
⟨64,204976218,204976335⟩]
theorem checked60106 : checkPrefixCuts (2^48) 7882145793 10 Manual.Count131072.C060106.packed 64 cuts60106 = true := by
 decide +kernel
def pointBounds60106 : List (Nat × Nat × Nat) := [(7882242048,113938723850001,113939112269735)]
theorem point_links_checked60106 : (cuts60106.take 1).map (fun c => (7882145793-1+2*2^10*c.k,113938573117159+c.lower,113938961536808+c.upper)) = pointBounds60106 := by
 decide +kernel
def cuts60107 : List PrefixCut := [⟨64,204401456,204401563⟩]
theorem checked60107 : checkPrefixCuts (2^48) 7882276865 10 Manual.Count131072.C060107.packed 64 cuts60107 = true := by
 decide +kernel
def cuts60108 : List PrefixCut := [⟨40,130659478,130659552⟩,
⟨64,208111797,208111917⟩]
theorem checked60108 : checkPrefixCuts (2^48) 7882407937 10 Manual.Count131072.C060108.packed 64 cuts60108 = true := by
 decide +kernel
def pointBounds60108 : List (Nat × Nat × Nat) := [(7882489856,113939113154311,113939501574258)]
theorem point_links_checked60108 : (cuts60108.take 1).map (fun c => (7882407937-1+2*2^10*c.k,113938982494833+c.lower,113939370914706+c.upper)) = pointBounds60108 := by
 decide +kernel
def cuts60109 : List PrefixCut := [⟨64,199002695,199002814⟩]
theorem checked60109 : checkPrefixCuts (2^48) 7882539009 10 Manual.Count131072.C060109.packed 64 cuts60109 = true := by
 decide +kernel
def cuts60110 : List PrefixCut := [⟨33,105802544,105802605⟩,
⟨64,206997928,206998046⟩]
theorem checked60110 : checkPrefixCuts (2^48) 7882670081 10 Manual.Count131072.C060110.packed 64 cuts60110 = true := by
 decide +kernel
def pointBounds60110 : List (Nat × Nat × Nat) := [(7882737664,113939495411869,113939883832042)]
theorem point_links_checked60110 : (cuts60110.take 1).map (fun c => (7882670081-1+2*2^10*c.k,113939389609325+c.lower,113939778029437+c.upper)) = pointBounds60110 := by
 decide +kernel
def cuts60111 : List PrefixCut := [⟨64,206208936,206209053⟩]
theorem checked60111 : checkPrefixCuts (2^48) 7882801153 10 Manual.Count131072.C060111.packed 64 cuts60111 = true := by
 decide +kernel
def cuts60112 : List PrefixCut := [⟨26,85589096,85589146⟩,
⟨64,207990840,207990962⟩]
theorem checked60112 : checkPrefixCuts (2^48) 7882932225 10 Manual.Count131072.C060112.packed 64 cuts60112 = true := by
 decide +kernel
def pointBounds60112 : List (Nat × Nat × Nat) := [(7882985472,113939888405285,113940276825682)]
theorem point_links_checked60112 : (cuts60112.take 1).map (fun c => (7882932225-1+2*2^10*c.k,113939802816189+c.lower,113940191236536+c.upper)) = pointBounds60112 := by
 decide +kernel
def cuts60113 : List PrefixCut := [⟨64,207737436,207737554⟩]
theorem checked60113 : checkPrefixCuts (2^48) 7883063297 10 Manual.Count131072.C060113.packed 64 cuts60113 = true := by
 decide +kernel
def cuts60114 : List PrefixCut := [⟨19,61842104,61842140⟩,
⟨64,205341741,205341861⟩]
theorem checked60114 : checkPrefixCuts (2^48) 7883194369 10 Manual.Count131072.C060114.packed 64 cuts60114 = true := by
 decide +kernel
def pointBounds60114 : List (Nat × Nat × Nat) := [(7883233280,113940280386569,113940668807192)]
theorem point_links_checked60114 : (cuts60114.take 1).map (fun c => (7883194369-1+2*2^10*c.k,113940218544465+c.lower,113940606965052+c.upper)) = pointBounds60114 := by
 decide +kernel
def cuts60115 : List PrefixCut := [⟨64,207123549,207123665⟩]
theorem checked60115 : checkPrefixCuts (2^48) 7883325441 10 Manual.Count131072.C060115.packed 64 cuts60115 = true := by
 decide +kernel
def cuts60116 : List PrefixCut := [⟨12,38025234,38025257⟩,
⟨64,207370011,207370133⟩]
theorem checked60116 : checkPrefixCuts (2^48) 7883456513 10 Manual.Count131072.C060116.packed 64 cuts60116 = true := by
 decide +kernel
def pointBounds60116 : List (Nat × Nat × Nat) := [(7883481088,113940669034989,113941057455835)]
theorem point_links_checked60116 : (cuts60116.take 1).map (fun c => (7883456513-1+2*2^10*c.k,113940631009755+c.lower,113941019430578+c.upper)) = pointBounds60116 := by
 decide +kernel
def cuts60117 : List PrefixCut := [⟨64,204081866,204081983⟩]
theorem checked60117 : checkPrefixCuts (2^48) 7883587585 10 Manual.Count131072.C060117.packed 64 cuts60117 = true := by
 decide +kernel
def cuts60118 : List PrefixCut := [⟨5,16423515,16423525⟩,
⟨64,203435802,203435921⟩]
theorem checked60118 : checkPrefixCuts (2^48) 7883718657 10 Manual.Count131072.C060118.packed 64 cuts60118 = true := by
 decide +kernel
def pointBounds60118 : List (Nat × Nat × Nat) := [(7883728896,113941058885147,113941447306219)]
theorem point_links_checked60118 : (cuts60118.take 1).map (fun c => (7883718657-1+2*2^10*c.k,113941042461632+c.lower,113941430882694+c.upper)) = pointBounds60118 := by
 decide +kernel
def cuts60119 : List PrefixCut := [⟨62,197077436,197077552⟩,
⟨64,203325310,203325430⟩]
theorem checked60119 : checkPrefixCuts (2^48) 7883849729 10 Manual.Count131072.C060119.packed 64 cuts60119 = true := by
 decide +kernel
def pointBounds60119 : List (Nat × Nat × Nat) := [(7883976704,113941442974870,113941831396167)]
theorem point_links_checked60119 : (cuts60119.take 1).map (fun c => (7883849729-1+2*2^10*c.k,113941245897434+c.lower,113941634318615+c.upper)) = pointBounds60119 := by
 decide +kernel
def cuts60120 : List PrefixCut := [⟨64,204607191,204607307⟩]
theorem checked60120 : checkPrefixCuts (2^48) 7883980801 10 Manual.Count131072.C060120.packed 64 cuts60120 = true := by
 decide +kernel
def cuts60121 : List PrefixCut := [⟨55,177935182,177935282⟩,
⟨64,207102886,207103003⟩]
theorem checked60121 : checkPrefixCuts (2^48) 7884111873 10 Manual.Count131072.C060121.packed 64 cuts60121 = true := by
 decide +kernel
def pointBounds60121 : List (Nat × Nat × Nat) := [(7884224512,113941831765117,113942220186634)]
theorem point_links_checked60121 : (cuts60121.take 1).map (fun c => (7884111873-1+2*2^10*c.k,113941653829935+c.lower,113942042251352+c.upper)) = pointBounds60121 := by
 decide +kernel
def cuts60122 : List PrefixCut := [⟨64,205885609,205885726⟩]
theorem checked60122 : checkPrefixCuts (2^48) 7884242945 10 Manual.Count131072.C060122.packed 64 cuts60122 = true := by
 decide +kernel
def cuts60123 : List PrefixCut := [⟨48,154153137,154153226⟩,
⟨64,204061501,204061617⟩]
theorem checked60123 : checkPrefixCuts (2^48) 7884374017 10 Manual.Count131072.C060123.packed 64 cuts60123 = true := by
 decide +kernel
def pointBounds60123 : List (Nat × Nat × Nat) := [(7884472320,113942220971567,113942609393307)]
theorem point_links_checked60123 : (cuts60123.take 1).map (fun c => (7884374017-1+2*2^10*c.k,113942066818430+c.lower,113942455240081+c.upper)) = pointBounds60123 := by
 decide +kernel
def cuts60124 : List PrefixCut := [⟨64,206949745,206949863⟩]
theorem checked60124 : checkPrefixCuts (2^48) 7884505089 10 Manual.Count131072.C060124.packed 64 cuts60124 = true := by
 decide +kernel
def cuts60125 : List PrefixCut := [⟨41,131979095,131979172⟩,
⟨64,204483105,204483223⟩]
theorem checked60125 : checkPrefixCuts (2^48) 7884636161 10 Manual.Count131072.C060125.packed 64 cuts60125 = true := by
 decide +kernel
def pointBounds60125 : List (Nat × Nat × Nat) := [(7884720128,113942609808771,113942998230733)]
theorem point_links_checked60125 : (cuts60125.take 1).map (fun c => (7884636161-1+2*2^10*c.k,113942477829676+c.lower,113942866251561+c.upper)) = pointBounds60125 := by
 decide +kernel
def cuts60126 : List PrefixCut := [⟨64,208049532,208049647⟩]
theorem checked60126 : checkPrefixCuts (2^48) 7884767233 10 Manual.Count131072.C060126.packed 64 cuts60126 = true := by
 decide +kernel
def cuts60127 : List PrefixCut := [⟨34,112555209,112555273⟩,
⟨64,207082244,207082364⟩]
theorem checked60127 : checkPrefixCuts (2^48) 7884898305 10 Manual.Count131072.C060127.packed 64 cuts60127 = true := by
 decide +kernel
def pointBounds60127 : List (Nat × Nat × Nat) := [(7884967936,113943002917522,113943391339704)]
theorem point_links_checked60127 : (cuts60127.take 1).map (fun c => (7884898305-1+2*2^10*c.k,113942890362313+c.lower,113943278784431+c.upper)) = pointBounds60127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000003
