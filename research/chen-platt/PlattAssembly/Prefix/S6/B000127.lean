import PlattAssemblyKernel
import PlattCertificates.Count131072.C054064
import PlattCertificates.Count131072.C054065
import PlattCertificates.Count131072.C054066
import PlattCertificates.Count131072.C054067
import PlattCertificates.Count131072.C054068
import PlattCertificates.Count131072.C054069
import PlattCertificates.Count131072.C054070
import PlattCertificates.Count131072.C054071
import PlattCertificates.Count131072.C054072
import PlattCertificates.Count131072.C054073
import PlattCertificates.Count131072.C054074
import PlattCertificates.Count131072.C054075
import PlattCertificates.Count131072.C054076
import PlattCertificates.Count131072.C054077
import PlattCertificates.Count131072.C054078
import PlattCertificates.Count131072.C054079
import PlattCertificates.Count131072.C054080
import PlattCertificates.Count131072.C054081
import PlattCertificates.Count131072.C054082
import PlattCertificates.Count131072.C054083
import PlattCertificates.Count131072.C054084
import PlattCertificates.Count131072.C054085
import PlattCertificates.Count131072.C054086
import PlattCertificates.Count131072.C054087
import PlattCertificates.Count131072.C054088
import PlattCertificates.Count131072.C054089
import PlattCertificates.Count131072.C054090
import PlattCertificates.Count131072.C054091
import PlattCertificates.Count131072.C054092
import PlattCertificates.Count131072.C054093
import PlattCertificates.Count131072.C054094
import PlattCertificates.Count131072.C054095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54064 : List PrefixCut := [⟨64,232118475,232118606⟩]
theorem checked54064 : checkPrefixCuts (2^48) 7090208769 10 Manual.Count131072.C054064.packed 64 cuts54064 = true := by
 decide +kernel
def cuts54065 : List PrefixCut := [⟨41,145771525,145771608⟩,
⟨64,230129273,230129403⟩]
theorem checked54065 : checkPrefixCuts (2^48) 7090339841 10 Manual.Count131072.C054065.packed 64 cuts54065 = true := by
 decide +kernel
def pointBounds54065 : List (Nat × Nat × Nat) := [(7090423808,112628125672361,112628513346396)]
theorem point_links_checked54065 : (cuts54065.take 1).map (fun c => (7090339841-1+2*2^10*c.k,112627979900836+c.lower,112628367574788+c.upper)) = pointBounds54065 := by
 decide +kernel
def cuts54066 : List PrefixCut := [⟨64,233499310,233499439⟩]
theorem checked54066 : checkPrefixCuts (2^48) 7090470913 10 Manual.Count131072.C054066.packed 64 cuts54066 = true := by
 decide +kernel
def cuts54067 : List PrefixCut := [⟨22,78559907,78559951⟩,
⟨64,225912960,225913087⟩]
theorem checked54067 : checkPrefixCuts (2^48) 7090601985 10 Manual.Count131072.C054067.packed 64 cuts54067 = true := by
 decide +kernel
def pointBounds54067 : List (Nat × Nat × Nat) := [(7090647040,112628522089326,112628909763581)]
theorem point_links_checked54067 : (cuts54067.take 1).map (fun c => (7090601985-1+2*2^10*c.k,112628443529419+c.lower,112628831203630+c.upper)) = pointBounds54067 := by
 decide +kernel
def cuts54068 : List PrefixCut := [⟨64,231148612,231148744⟩]
theorem checked54068 : checkPrefixCuts (2^48) 7090733057 10 Manual.Count131072.C054068.packed 64 cuts54068 = true := by
 decide +kernel
def cuts54069 : List PrefixCut := [⟨3,10638371,10638377⟩,
⟨64,228246612,228246744⟩]
theorem checked54069 : checkPrefixCuts (2^48) 7090864129 10 Manual.Count131072.C054069.packed 64 cuts54069 = true := by
 decide +kernel
def pointBounds54069 : List (Nat × Nat × Nat) := [(7090870272,112628911229362,112629298903838)]
theorem point_links_checked54069 : (cuts54069.take 1).map (fun c => (7090864129-1+2*2^10*c.k,112628900590991+c.lower,112629288265461+c.upper)) = pointBounds54069 := by
 decide +kernel
def cuts54070 : List PrefixCut := [⟨48,171440205,171440304⟩,
⟨64,228639336,228639467⟩]
theorem checked54070 : checkPrefixCuts (2^48) 7090995201 10 Manual.Count131072.C054070.packed 64 cuts54070 = true := by
 decide +kernel
def pointBounds54070 : List (Nat × Nat × Nat) := [(7091093504,112629300277808,112629687952509)]
theorem point_links_checked54070 : (cuts54070.take 1).map (fun c => (7090995201-1+2*2^10*c.k,112629128837603+c.lower,112629516512205+c.upper)) = pointBounds54070 := by
 decide +kernel
def cuts54071 : List PrefixCut := [⟨64,226650438,226650563⟩]
theorem checked54071 : checkPrefixCuts (2^48) 7091126273 10 Manual.Count131072.C054071.packed 64 cuts54071 = true := by
 decide +kernel
def cuts54072 : List PrefixCut := [⟨29,103479816,103479875⟩,
⟨64,225931783,225931914⟩]
theorem checked54072 : checkPrefixCuts (2^48) 7091257345 10 Manual.Count131072.C054072.packed 64 cuts54072 = true := by
 decide +kernel
def pointBounds54072 : List (Nat × Nat × Nat) := [(7091316736,112629687607193,112630075282110)]
theorem point_links_checked54072 : (cuts54072.take 1).map (fun c => (7091257345-1+2*2^10*c.k,112629584127377+c.lower,112629971802235+c.upper)) = pointBounds54072 := by
 decide +kernel
def cuts54073 : List PrefixCut := [⟨64,230174649,230174779⟩]
theorem checked54073 : checkPrefixCuts (2^48) 7091388417 10 Manual.Count131072.C054073.packed 64 cuts54073 = true := by
 decide +kernel
def cuts54074 : List PrefixCut := [⟨10,34889006,34889026⟩,
⟨64,225328031,225328162⟩]
theorem checked54074 : checkPrefixCuts (2^48) 7091519489 10 Manual.Count131072.C054074.packed 64 cuts54074 = true := by
 decide +kernel
def pointBounds54074 : List (Nat × Nat × Nat) := [(7091539968,112630075122815,112630462797954)]
theorem point_links_checked54074 : (cuts54074.take 1).map (fun c => (7091519489-1+2*2^10*c.k,112630040233809+c.lower,112630427908928+c.upper)) = pointBounds54074 := by
 decide +kernel
def cuts54075 : List PrefixCut := [⟨55,195714890,195715003⟩,
⟨64,228499115,228499246⟩]
theorem checked54075 : checkPrefixCuts (2^48) 7091650561 10 Manual.Count131072.C054075.packed 64 cuts54075 = true := by
 decide +kernel
def pointBounds54075 : List (Nat × Nat × Nat) := [(7091763200,112630461276730,112630848952093)]
theorem point_links_checked54075 : (cuts54075.take 1).map (fun c => (7091650561-1+2*2^10*c.k,112630265561840+c.lower,112630653237090+c.upper)) = pointBounds54075 := by
 decide +kernel
def cuts54076 : List PrefixCut := [⟨64,230796929,230797058⟩]
theorem checked54076 : checkPrefixCuts (2^48) 7091781633 10 Manual.Count131072.C054076.packed 64 cuts54076 = true := by
 decide +kernel
def cuts54077 : List PrefixCut := [⟨36,130101689,130101761⟩,
⟨64,230395757,230395886⟩]
theorem checked54077 : checkPrefixCuts (2^48) 7091912705 10 Manual.Count131072.C054077.packed 64 cuts54077 = true := by
 decide +kernel
def pointBounds54077 : List (Nat × Nat × Nat) := [(7091986432,112630854959573,112631242635155)]
theorem point_links_checked54077 : (cuts54077.take 1).map (fun c => (7091912705-1+2*2^10*c.k,112630724857884+c.lower,112631112533394+c.upper)) = pointBounds54077 := by
 decide +kernel
def cuts54078 : List PrefixCut := [⟨64,227811745,227811873⟩]
theorem checked54078 : checkPrefixCuts (2^48) 7092043777 10 Manual.Count131072.C054078.packed 64 cuts54078 = true := by
 decide +kernel
def cuts54079 : List PrefixCut := [⟨17,62270467,62270501⟩,
⟨64,231538202,231538332⟩]
theorem checked54079 : checkPrefixCuts (2^48) 7092174849 10 Manual.Count131072.C054079.packed 64 cuts54079 = true := by
 decide +kernel
def pointBounds54079 : List (Nat × Nat × Nat) := [(7092209664,112631245335853,112631633011654)]
theorem point_links_checked54079 : (cuts54079.take 1).map (fun c => (7092174849-1+2*2^10*c.k,112631183065386+c.lower,112631570741153+c.upper)) = pointBounds54079 := by
 decide +kernel
def cuts54080 : List PrefixCut := [⟨62,224191892,224192017⟩,
⟨64,231454547,231454676⟩]
theorem checked54080 : checkPrefixCuts (2^48) 7092305921 10 Manual.Count131072.C054080.packed 64 cuts54080 = true := by
 decide +kernel
def pointBounds54080 : List (Nat × Nat × Nat) := [(7092432896,112631638795480,112632026471502)]
theorem point_links_checked54080 : (cuts54080.take 1).map (fun c => (7092305921-1+2*2^10*c.k,112631414603588+c.lower,112631802279485+c.upper)) = pointBounds54080 := by
 decide +kernel
def cuts54081 : List PrefixCut := [⟨64,229823120,229823251⟩]
theorem checked54081 : checkPrefixCuts (2^48) 7092436993 10 Manual.Count131072.C054081.packed 64 cuts54081 = true := by
 decide +kernel
def cuts54082 : List PrefixCut := [⟨43,149932381,149932468⟩,
⟨64,224699447,224699577⟩]
theorem checked54082 : checkPrefixCuts (2^48) 7092568065 10 Manual.Count131072.C054082.packed 64 cuts54082 = true := by
 decide +kernel
def pointBounds54082 : List (Nat × Nat × Nat) := [(7092656128,112632025813636,112632413489880)]
theorem point_links_checked54082 : (cuts54082.take 1).map (fun c => (7092568065-1+2*2^10*c.k,112631875881255+c.lower,112632263557412+c.upper)) = pointBounds54082 := by
 decide +kernel
def cuts54083 : List PrefixCut := [⟨64,231005179,231005312⟩]
theorem checked54083 : checkPrefixCuts (2^48) 7092699137 10 Manual.Count131072.C054083.packed 64 cuts54083 = true := by
 decide +kernel
def cuts54084 : List PrefixCut := [⟨24,86670485,86670533⟩,
⟨64,228183348,228183476⟩]
theorem checked54084 : checkPrefixCuts (2^48) 7092830209 10 Manual.Count131072.C054084.packed 64 cuts54084 = true := by
 decide +kernel
def pointBounds54084 : List (Nat × Nat × Nat) := [(7092879360,112632418256366,112632805932834)]
theorem point_links_checked54084 : (cuts54084.take 1).map (fun c => (7092830209-1+2*2^10*c.k,112632331585881+c.lower,112632719262301+c.upper)) = pointBounds54084 := by
 decide +kernel
def cuts54085 : List PrefixCut := [⟨64,228814055,228814186⟩]
theorem checked54085 : checkPrefixCuts (2^48) 7092961281 10 Manual.Count131072.C054085.packed 64 cuts54085 = true := by
 decide +kernel
def cuts54086 : List PrefixCut := [⟨5,18690660,18690671⟩,
⟨64,230238413,230238547⟩]
theorem checked54086 : checkPrefixCuts (2^48) 7093092353 10 Manual.Count131072.C054086.packed 64 cuts54086 = true := by
 decide +kernel
def pointBounds54086 : List (Nat × Nat × Nat) := [(7093102592,112632807273944,112633194950634)]
theorem point_links_checked54086 : (cuts54086.take 1).map (fun c => (7093092353-1+2*2^10*c.k,112632788583284+c.lower,112633176259963+c.upper)) = pointBounds54086 := by
 decide +kernel
def cuts54087 : List PrefixCut := [⟨50,179917915,179918015⟩,
⟨64,229956377,229956506⟩]
theorem checked54087 : checkPrefixCuts (2^48) 7093223425 10 Manual.Count131072.C054087.packed 64 cuts54087 = true := by
 decide +kernel
def pointBounds54087 : List (Nat × Nat × Nat) := [(7093325824,112633198739612,112633586416525)]
theorem point_links_checked54087 : (cuts54087.take 1).map (fun c => (7093223425-1+2*2^10*c.k,112633018821697+c.lower,112633406498510+c.upper)) = pointBounds54087 := by
 decide +kernel
def cuts54088 : List PrefixCut := [⟨64,229595015,229595145⟩]
theorem checked54088 : checkPrefixCuts (2^48) 7093354497 10 Manual.Count131072.C054088.packed 64 cuts54088 = true := by
 decide +kernel
def cuts54089 : List PrefixCut := [⟨31,113288069,113288133⟩,
⟨64,233479440,233479572⟩]
theorem checked54089 : checkPrefixCuts (2^48) 7093485569 10 Manual.Count131072.C054089.packed 64 cuts54089 = true := by
 decide +kernel
def pointBounds54089 : List (Nat × Nat × Nat) := [(7093549056,112633591661158,112633979338294)]
theorem point_links_checked54089 : (cuts54089.take 1).map (fun c => (7093485569-1+2*2^10*c.k,112633478373089+c.lower,112633866050161+c.upper)) = pointBounds54089 := by
 decide +kernel
def cuts54090 : List PrefixCut := [⟨64,225935994,225936125⟩]
theorem checked54090 : checkPrefixCuts (2^48) 7093616641 10 Manual.Count131072.C054090.packed 64 cuts54090 = true := by
 decide +kernel
def cuts54091 : List PrefixCut := [⟨12,43726507,43726532⟩,
⟨64,230415544,230415677⟩]
theorem checked54091 : checkPrefixCuts (2^48) 7093747713 10 Manual.Count131072.C054091.packed 64 cuts54091 = true := by
 decide +kernel
def pointBounds54091 : List (Nat × Nat × Nat) := [(7093772288,112633981515030,112634369192390)]
theorem point_links_checked54091 : (cuts54091.take 1).map (fun c => (7093747713-1+2*2^10*c.k,112633937788523+c.lower,112634325465858+c.upper)) = pointBounds54091 := by
 decide +kernel
def cuts54092 : List PrefixCut := [⟨57,204779370,204779485⟩,
⟨64,228982870,228982999⟩]
theorem checked54092 : checkPrefixCuts (2^48) 7093878785 10 Manual.Count131072.C054092.packed 64 cuts54092 = true := by
 decide +kernel
def pointBounds54092 : List (Nat × Nat × Nat) := [(7093995520,112634372983437,112634760661020)]
theorem point_links_checked54092 : (cuts54092.take 1).map (fun c => (7093878785-1+2*2^10*c.k,112634168204067+c.lower,112634555881535+c.upper)) = pointBounds54092 := by
 decide +kernel
def cuts54093 : List PrefixCut := [⟨64,227510552,227510682⟩]
theorem checked54093 : checkPrefixCuts (2^48) 7094009857 10 Manual.Count131072.C054093.packed 64 cuts54093 = true := by
 decide +kernel
def cuts54094 : List PrefixCut := [⟨38,138948427,138948507⟩,
⟨64,231632756,231632889⟩]
theorem checked54094 : checkPrefixCuts (2^48) 7094140929 10 Manual.Count131072.C054094.packed 64 cuts54094 = true := by
 decide +kernel
def pointBounds54094 : List (Nat × Nat × Nat) := [(7094218752,112634763645916,112635151323723)]
theorem point_links_checked54094 : (cuts54094.take 1).map (fun c => (7094140929-1+2*2^10*c.k,112634624697489+c.lower,112635012375216+c.upper)) = pointBounds54094 := by
 decide +kernel
def cuts54095 : List PrefixCut := [⟨64,230160453,230160581⟩]
theorem checked54095 : checkPrefixCuts (2^48) 7094272001 10 Manual.Count131072.C054095.packed 64 cuts54095 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000127
