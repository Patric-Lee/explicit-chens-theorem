import PlattAssemblyKernel
import PlattCertificates.Count131072.C057040
import PlattCertificates.Count131072.C057041
import PlattCertificates.Count131072.C057042
import PlattCertificates.Count131072.C057043
import PlattCertificates.Count131072.C057044
import PlattCertificates.Count131072.C057045
import PlattCertificates.Count131072.C057046
import PlattCertificates.Count131072.C057047
import PlattCertificates.Count131072.C057048
import PlattCertificates.Count131072.C057049
import PlattCertificates.Count131072.C057050
import PlattCertificates.Count131072.C057051
import PlattCertificates.Count131072.C057052
import PlattCertificates.Count131072.C057053
import PlattCertificates.Count131072.C057054
import PlattCertificates.Count131072.C057055
import PlattCertificates.Count131072.C057056
import PlattCertificates.Count131072.C057057
import PlattCertificates.Count131072.C057058
import PlattCertificates.Count131072.C057059
import PlattCertificates.Count131072.C057060
import PlattCertificates.Count131072.C057061
import PlattCertificates.Count131072.C057062
import PlattCertificates.Count131072.C057063
import PlattCertificates.Count131072.C057064
import PlattCertificates.Count131072.C057065
import PlattCertificates.Count131072.C057066
import PlattCertificates.Count131072.C057067
import PlattCertificates.Count131072.C057068
import PlattCertificates.Count131072.C057069
import PlattCertificates.Count131072.C057070
import PlattCertificates.Count131072.C057071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts57040 : List PrefixCut := [⟨64,212300580,212300704⟩]
theorem checked57040 : checkPrefixCuts (2^48) 7480279041 10 Manual.Count131072.C057040.packed 64 cuts57040 = true := by
 decide +kernel
def cuts57041 : List PrefixCut := [⟨27,92527575,92527626⟩,
⟨64,220988888,220989013⟩]
theorem checked57041 : checkPrefixCuts (2^48) 7480410113 10 Manual.Count131072.C057041.packed 64 cuts57041 = true := by
 decide +kernel
def pointBounds57041 : List (Nat × Nat × Nat) := [(7480465408,113291818788816,113292206839742)]
theorem point_links_checked57041 : (cuts57041.take 1).map (fun c => (7480410113-1+2*2^10*c.k,113291726261241+c.lower,113292114312116+c.upper)) = pointBounds57041 := by
 decide +kernel
def cuts57042 : List PrefixCut := [⟨64,210976181,210976306⟩]
theorem checked57042 : checkPrefixCuts (2^48) 7480541185 10 Manual.Count131072.C057042.packed 64 cuts57042 = true := by
 decide +kernel
def cuts57043 : List PrefixCut := [⟨14,46582079,46582106⟩,
⟨64,220642488,220642612⟩]
theorem checked57043 : checkPrefixCuts (2^48) 7480672257 10 Manual.Count131072.C057043.packed 64 cuts57043 = true := by
 decide +kernel
def pointBounds57043 : List (Nat × Nat × Nat) := [(7480700928,113292204808389,113292592859541)]
theorem point_links_checked57043 : (cuts57043.take 1).map (fun c => (7480672257-1+2*2^10*c.k,113292158226310+c.lower,113292546277435+c.upper)) = pointBounds57043 := by
 decide +kernel
def cuts57044 : List PrefixCut := [⟨64,216236417,216236543⟩]
theorem checked57044 : checkPrefixCuts (2^48) 7480803329 10 Manual.Count131072.C057044.packed 64 cuts57044 = true := by
 decide +kernel
def cuts57045 : List PrefixCut := [⟨1,3235804,3235806⟩,
⟨64,216006870,216006995⟩]
theorem checked57045 : checkPrefixCuts (2^48) 7480934401 10 Manual.Count131072.C057045.packed 64 cuts57045 = true := by
 decide +kernel
def pointBounds57045 : List (Nat × Nat × Nat) := [(7480936448,113292598341019,113292986392396)]
theorem point_links_checked57045 : (cuts57045.take 1).map (fun c => (7480934401-1+2*2^10*c.k,113292595105215+c.lower,113292983156590+c.upper)) = pointBounds57045 := by
 decide +kernel
def cuts57046 : List PrefixCut := [⟨52,178980732,178980833⟩,
⟨64,220254673,220254796⟩]
theorem checked57046 : checkPrefixCuts (2^48) 7481065473 10 Manual.Count131072.C057046.packed 64 cuts57046 = true := by
 decide +kernel
def pointBounds57046 : List (Nat × Nat × Nat) := [(7481171968,113292990092817,113293378144418)]
theorem point_links_checked57046 : (cuts57046.take 1).map (fun c => (7481065473-1+2*2^10*c.k,113292811112085+c.lower,113293199163585+c.upper)) = pointBounds57046 := by
 decide +kernel
def cuts57047 : List PrefixCut := [⟨64,217918131,217918252⟩]
theorem checked57047 : checkPrefixCuts (2^48) 7481196545 10 Manual.Count131072.C057047.packed 64 cuts57047 = true := by
 decide +kernel
def cuts57048 : List PrefixCut := [⟨39,132434568,132434642⟩,
⟨64,215506425,215506548⟩]
theorem checked57048 : checkPrefixCuts (2^48) 7481327617 10 Manual.Count131072.C057048.packed 64 cuts57048 = true := by
 decide +kernel
def pointBounds57048 : List (Nat × Nat × Nat) := [(7481407488,113293381719457,113293769771275)]
theorem point_links_checked57048 : (cuts57048.take 1).map (fun c => (7481327617-1+2*2^10*c.k,113293249284889+c.lower,113293637336633+c.upper)) = pointBounds57048 := by
 decide +kernel
def cuts57049 : List PrefixCut := [⟨64,217835247,217835371⟩]
theorem checked57049 : checkPrefixCuts (2^48) 7481458689 10 Manual.Count131072.C057049.packed 64 cuts57049 = true := by
 decide +kernel
def cuts57050 : List PrefixCut := [⟨26,89089377,89089428⟩,
⟨64,217568080,217568205⟩]
theorem checked57050 : checkPrefixCuts (2^48) 7481589761 10 Manual.Count131072.C057050.packed 64 cuts57050 = true := by
 decide +kernel
def pointBounds57050 : List (Nat × Nat × Nat) := [(7481643008,113293771715938,113294159767980)]
theorem point_links_checked57050 : (cuts57050.take 1).map (fun c => (7481589761-1+2*2^10*c.k,113293682626561+c.lower,113294070678552+c.upper)) = pointBounds57050 := by
 decide +kernel
def cuts57051 : List PrefixCut := [⟨64,216586096,216586215⟩]
theorem checked57051 : checkPrefixCuts (2^48) 7481720833 10 Manual.Count131072.C057051.packed 64 cuts57051 = true := by
 decide +kernel
def cuts57052 : List PrefixCut := [⟨13,43188853,43188876⟩,
⟨64,218463349,218463471⟩]
theorem checked57052 : checkPrefixCuts (2^48) 7481851905 10 Manual.Count131072.C057052.packed 64 cuts57052 = true := by
 decide +kernel
def pointBounds57052 : List (Nat × Nat × Nat) := [(7481878528,113294159969590,113294548021848)]
theorem point_links_checked57052 : (cuts57052.take 1).map (fun c => (7481851905-1+2*2^10*c.k,113294116780737+c.lower,113294504832972+c.upper)) = pointBounds57052 := by
 decide +kernel
def cuts57053 : List PrefixCut := [⟨64,216014206,216014330⟩]
theorem checked57053 : checkPrefixCuts (2^48) 7481982977 10 Manual.Count131072.C057053.packed 64 cuts57053 = true := by
 decide +kernel
def pointBounds57053 : List (Nat × Nat × Nat) := [(7482114048,113294551258292,113294939310773)]
theorem point_links_checked57053 : (cuts57053.take 1).map (fun c => (7481982977-1+2*2^10*c.k,113294335244086+c.lower,113294723296443+c.upper)) = pointBounds57053 := by
 decide +kernel
def cuts57054 : List PrefixCut := [⟨64,213790892,213791017⟩]
theorem checked57054 : checkPrefixCuts (2^48) 7482114049 10 Manual.Count131072.C057054.packed 64 cuts57054 = true := by
 decide +kernel
def cuts57055 : List PrefixCut := [⟨51,174137347,174137447⟩,
⟨64,217511421,217511547⟩]
theorem checked57055 : checkPrefixCuts (2^48) 7482245121 10 Manual.Count131072.C057055.packed 64 cuts57055 = true := by
 decide +kernel
def pointBounds57055 : List (Nat × Nat × Nat) := [(7482349568,113294939186531,113295327239237)]
theorem point_links_checked57055 : (cuts57055.take 1).map (fun c => (7482245121-1+2*2^10*c.k,113294765049184+c.lower,113295153101790+c.upper)) = pointBounds57055 := by
 decide +kernel
def cuts57056 : List PrefixCut := [⟨64,216567148,216567273⟩]
theorem checked57056 : checkPrefixCuts (2^48) 7482376193 10 Manual.Count131072.C057056.packed 64 cuts57056 = true := by
 decide +kernel
def cuts57057 : List PrefixCut := [⟨38,130984242,130984315⟩,
⟨64,221453609,221453734⟩]
theorem checked57057 : checkPrefixCuts (2^48) 7482507265 10 Manual.Count131072.C057057.packed 64 cuts57057 = true := by
 decide +kernel
def pointBounds57057 : List (Nat × Nat × Nat) := [(7482585088,113295330111995,113295718164925)]
theorem point_links_checked57057 : (cuts57057.take 1).map (fun c => (7482507265-1+2*2^10*c.k,113295199127753+c.lower,113295587180610+c.upper)) = pointBounds57057 := by
 decide +kernel
def cuts57058 : List PrefixCut := [⟨64,219456032,219456155⟩]
theorem checked57058 : checkPrefixCuts (2^48) 7482638337 10 Manual.Count131072.C057058.packed 64 cuts57058 = true := by
 decide +kernel
def cuts57059 : List PrefixCut := [⟨25,82342032,82342077⟩,
⟨64,213019834,213019950⟩]
theorem checked57059 : checkPrefixCuts (2^48) 7482769409 10 Manual.Count131072.C057059.packed 64 cuts57059 = true := by
 decide +kernel
def pointBounds57059 : List (Nat × Nat × Nat) := [(7482820608,113295722379426,113296110432576)]
theorem point_links_checked57059 : (cuts57059.take 1).map (fun c => (7482769409-1+2*2^10*c.k,113295640037394+c.lower,113296028090499+c.upper)) = pointBounds57059 := by
 decide +kernel
def cuts57060 : List PrefixCut := [⟨64,215536344,215536463⟩]
theorem checked57060 : checkPrefixCuts (2^48) 7482900481 10 Manual.Count131072.C057060.packed 64 cuts57060 = true := by
 decide +kernel
def cuts57061 : List PrefixCut := [⟨12,39947157,39947180⟩,
⟨64,216585772,216585889⟩]
theorem checked57061 : checkPrefixCuts (2^48) 7483031553 10 Manual.Count131072.C057061.packed 64 cuts57061 = true := by
 decide +kernel
def pointBounds57061 : List (Nat × Nat × Nat) := [(7483056128,113296108540729,113296496594092)]
theorem point_links_checked57061 : (cuts57061.take 1).map (fun c => (7483031553-1+2*2^10*c.k,113296068593572+c.lower,113296456646912+c.upper)) = pointBounds57061 := by
 decide +kernel
def cuts57062 : List PrefixCut := [⟨63,211052739,211052862⟩,
⟨64,214400365,214400490⟩]
theorem checked57062 : checkPrefixCuts (2^48) 7483162625 10 Manual.Count131072.C057062.packed 64 cuts57062 = true := by
 decide +kernel
def pointBounds57062 : List (Nat × Nat × Nat) := [(7483291648,113296496232083,113296884285663)]
theorem point_links_checked57062 : (cuts57062.take 1).map (fun c => (7483162625-1+2*2^10*c.k,113296285179344+c.lower,113296673232801+c.upper)) = pointBounds57062 := by
 decide +kernel
def cuts57063 : List PrefixCut := [⟨64,220113855,220113975⟩]
theorem checked57063 : checkPrefixCuts (2^48) 7483293697 10 Manual.Count131072.C057063.packed 64 cuts57063 = true := by
 decide +kernel
def cuts57064 : List PrefixCut := [⟨50,169069786,169069882⟩,
⟨64,216235896,216236020⟩]
theorem checked57064 : checkPrefixCuts (2^48) 7483424769 10 Manual.Count131072.C057064.packed 64 cuts57064 = true := by
 decide +kernel
def pointBounds57064 : List (Nat × Nat × Nat) := [(7483527168,113296888763350,113297276817148)]
theorem point_links_checked57064 : (cuts57064.take 1).map (fun c => (7483424769-1+2*2^10*c.k,113296719693564+c.lower,113297107747266+c.upper)) = pointBounds57064 := by
 decide +kernel
def cuts57065 : List PrefixCut := [⟨64,218940174,218940299⟩]
theorem checked57065 : checkPrefixCuts (2^48) 7483555841 10 Manual.Count131072.C057065.packed 64 cuts57065 = true := by
 decide +kernel
def cuts57066 : List PrefixCut := [⟨37,125171423,125171492⟩,
⟨64,217770380,217770503⟩]
theorem checked57066 : checkPrefixCuts (2^48) 7483686913 10 Manual.Count131072.C057066.packed 64 cuts57066 = true := by
 decide +kernel
def pointBounds57066 : List (Nat × Nat × Nat) := [(7483762688,113297280041057,113297668095077)]
theorem point_links_checked57066 : (cuts57066.take 1).map (fun c => (7483686913-1+2*2^10*c.k,113297154869634+c.lower,113297542923585+c.upper)) = pointBounds57066 := by
 decide +kernel
def cuts57067 : List PrefixCut := [⟨64,216638245,216638370⟩]
theorem checked57067 : checkPrefixCuts (2^48) 7483817985 10 Manual.Count131072.C057067.packed 64 cuts57067 = true := by
 decide +kernel
def cuts57068 : List PrefixCut := [⟨24,82667556,82667604⟩,
⟨64,217499493,217499620⟩]
theorem checked57068 : checkPrefixCuts (2^48) 7483949057 10 Manual.Count131072.C057068.packed 64 cuts57068 = true := by
 decide +kernel
def pointBounds57068 : List (Nat × Nat × Nat) := [(7483998208,113297671945815,113298060000062)]
theorem point_links_checked57068 : (cuts57068.take 1).map (fun c => (7483949057-1+2*2^10*c.k,113297589278259+c.lower,113297977332458+c.upper)) = pointBounds57068 := by
 decide +kernel
def cuts57069 : List PrefixCut := [⟨64,216179338,216179457⟩]
theorem checked57069 : checkPrefixCuts (2^48) 7484080129 10 Manual.Count131072.C057069.packed 64 cuts57069 = true := by
 decide +kernel
def cuts57070 : List PrefixCut := [⟨11,37533883,37533906⟩,
⟨64,217755131,217755254⟩]
theorem checked57070 : checkPrefixCuts (2^48) 7484211201 10 Manual.Count131072.C057070.packed 64 cuts57070 = true := by
 decide +kernel
def pointBounds57070 : List (Nat × Nat × Nat) := [(7484233728,113298060490973,113298448545441)]
theorem point_links_checked57070 : (cuts57070.take 1).map (fun c => (7484211201-1+2*2^10*c.k,113298022957090+c.lower,113298411011535+c.upper)) = pointBounds57070 := by
 decide +kernel
def cuts57071 : List PrefixCut := [⟨62,209289526,209289647⟩,
⟨64,215607645,215607770⟩]
theorem checked57071 : checkPrefixCuts (2^48) 7484342273 10 Manual.Count131072.C057071.packed 64 cuts57071 = true := by
 decide +kernel
def pointBounds57071 : List (Nat × Nat × Nat) := [(7484469248,113298450001747,113298838056436)]
theorem point_links_checked57071 : (cuts57071.take 1).map (fun c => (7484342273-1+2*2^10*c.k,113298240712221+c.lower,113298628766789+c.upper)) = pointBounds57071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000220
