import PlattAssemblyKernel
import PlattCertificates.Count131072.C066048
import PlattCertificates.Count131072.C066049
import PlattCertificates.Count131072.C066050
import PlattCertificates.Count131072.C066051
import PlattCertificates.Count131072.C066052
import PlattCertificates.Count131072.C066053
import PlattCertificates.Count131072.C066054
import PlattCertificates.Count131072.C066055
import PlattCertificates.Count131072.C066056
import PlattCertificates.Count131072.C066057
import PlattCertificates.Count131072.C066058
import PlattCertificates.Count131072.C066059
import PlattCertificates.Count131072.C066060
import PlattCertificates.Count131072.C066061
import PlattCertificates.Count131072.C066062
import PlattCertificates.Count131072.C066063
import PlattCertificates.Count131072.C066064
import PlattCertificates.Count131072.C066065
import PlattCertificates.Count131072.C066066
import PlattCertificates.Count131072.C066067
import PlattCertificates.Count131072.C066068
import PlattCertificates.Count131072.C066069
import PlattCertificates.Count131072.C066070
import PlattCertificates.Count131072.C066071
import PlattCertificates.Count131072.C066072
import PlattCertificates.Count131072.C066073
import PlattCertificates.Count131072.C066074
import PlattCertificates.Count131072.C066075
import PlattCertificates.Count131072.C066076
import PlattCertificates.Count131072.C066077
import PlattCertificates.Count131072.C066078
import PlattCertificates.Count131072.C066079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66048 : List PrefixCut := [⟨64,187064058,187064166⟩]
theorem checked66048 : checkPrefixCuts (2^48) 8660975617 10 Manual.Count131072.C066048.packed 64 cuts66048 = true := by
 decide +kernel
def cuts66049 : List PrefixCut := [⟨57,162135038,162135133⟩,
⟨64,182348954,182349061⟩]
theorem checked66049 : checkPrefixCuts (2^48) 8661106689 10 Manual.Count131072.C066049.packed 64 cuts66049 = true := by
 decide +kernel
def pointBounds66049 : List (Nat × Nat × Nat) := [(8661223424,115100486580084,115100875668400)]
theorem point_links_checked66049 : (cuts66049.take 1).map (fun c => (8661106689-1+2*2^10*c.k,115100324445046+c.lower,115100713533267+c.upper)) = pointBounds66049 := by
 decide +kernel
def cuts66050 : List PrefixCut := [⟨64,185693486,185693596⟩]
theorem checked66050 : checkPrefixCuts (2^48) 8661237761 10 Manual.Count131072.C066050.packed 64 cuts66050 = true := by
 decide +kernel
def cuts66051 : List PrefixCut := [⟨62,181953496,181953606⟩,
⟨64,187380538,187380650⟩]
theorem checked66051 : checkPrefixCuts (2^48) 8661368833 10 Manual.Count131072.C066051.packed 64 cuts66051 = true := by
 decide +kernel
def pointBounds66051 : List (Nat × Nat × Nat) := [(8661495808,115100874440982,115101263529530)]
theorem point_links_checked66051 : (cuts66051.take 1).map (fun c => (8661368833-1+2*2^10*c.k,115100692487486+c.lower,115101081575924+c.upper)) = pointBounds66051 := by
 decide +kernel
def cuts66052 : List PrefixCut := [⟨64,186077813,186077923⟩]
theorem checked66052 : checkPrefixCuts (2^48) 8661499905 10 Manual.Count131072.C066052.packed 64 cuts66052 = true := by
 decide +kernel
def cuts66053 : List PrefixCut := [⟨64,186139999,186140102⟩]
theorem checked66053 : checkPrefixCuts (2^48) 8661630977 10 Manual.Count131072.C066053.packed 64 cuts66053 = true := by
 decide +kernel
def cuts66054 : List PrefixCut := [⟨3,8319041,8319045⟩,
⟨64,184934818,184934927⟩]
theorem checked66054 : checkPrefixCuts (2^48) 8661762049 10 Manual.Count131072.C066054.packed 64 cuts66054 = true := by
 decide +kernel
def pointBounds66054 : List (Nat × Nat × Nat) := [(8661768192,115101260404877,115101649493644)]
theorem point_links_checked66054 : (cuts66054.take 1).map (fun c => (8661762049-1+2*2^10*c.k,115101252085836+c.lower,115101641174599+c.upper)) = pointBounds66054 := by
 decide +kernel
def cuts66055 : List PrefixCut := [⟨64,185614444,185614548⟩]
theorem checked66055 : checkPrefixCuts (2^48) 8661893121 10 Manual.Count131072.C066055.packed 64 cuts66055 = true := by
 decide +kernel
def cuts66056 : List PrefixCut := [⟨8,23039132,23039145⟩,
⟨64,186943929,186944039⟩]
theorem checked66056 : checkPrefixCuts (2^48) 8662024193 10 Manual.Count131072.C066056.packed 64 cuts66056 = true := by
 decide +kernel
def pointBounds66056 : List (Nat × Nat × Nat) := [(8662040576,115101645674230,115102034763219)]
theorem point_links_checked66056 : (cuts66056.take 1).map (fun c => (8662024193-1+2*2^10*c.k,115101622635098+c.lower,115102011724074+c.upper)) = pointBounds66056 := by
 decide +kernel
def cuts66057 : List PrefixCut := [⟨64,186096242,186096351⟩]
theorem checked66057 : checkPrefixCuts (2^48) 8662155265 10 Manual.Count131072.C066057.packed 64 cuts66057 = true := by
 decide +kernel
def cuts66058 : List PrefixCut := [⟨13,38213234,38213255⟩,
⟨64,189732753,189732868⟩]
theorem checked66058 : checkPrefixCuts (2^48) 8662286337 10 Manual.Count131072.C066058.packed 64 cuts66058 = true := by
 decide +kernel
def pointBounds66058 : List (Nat × Nat × Nat) := [(8662312960,115102033888503,115102422977719)]
theorem point_links_checked66058 : (cuts66058.take 1).map (fun c => (8662286337-1+2*2^10*c.k,115101995675269+c.lower,115102384764464+c.upper)) = pointBounds66058 := by
 decide +kernel
def cuts66059 : List PrefixCut := [⟨64,185148294,185148401⟩]
theorem checked66059 : checkPrefixCuts (2^48) 8662417409 10 Manual.Count131072.C066059.packed 64 cuts66059 = true := by
 decide +kernel
def cuts66060 : List PrefixCut := [⟨18,52736532,52736562⟩,
⟨64,185632886,185632996⟩]
theorem checked66060 : checkPrefixCuts (2^48) 8662548481 10 Manual.Count131072.C066060.packed 64 cuts66060 = true := by
 decide +kernel
def pointBounds66060 : List (Nat × Nat × Nat) := [(8662585344,115102423292848,115102812382295)]
theorem point_links_checked66060 : (cuts66060.take 1).map (fun c => (8662548481-1+2*2^10*c.k,115102370556316+c.lower,115102759645733+c.upper)) = pointBounds66060 := by
 decide +kernel
def cuts66061 : List PrefixCut := [⟨64,185402636,185402742⟩]
theorem checked66061 : checkPrefixCuts (2^48) 8662679553 10 Manual.Count131072.C066061.packed 64 cuts66061 = true := by
 decide +kernel
def cuts66062 : List PrefixCut := [⟨23,68493640,68493682⟩,
⟨64,189298876,189298989⟩]
theorem checked66062 : checkPrefixCuts (2^48) 8662810625 10 Manual.Count131072.C066062.packed 64 cuts66062 = true := by
 decide +kernel
def pointBounds66062 : List (Nat × Nat × Nat) := [(8662857728,115102810085478,115103199175153)]
theorem point_links_checked66062 : (cuts66062.take 1).map (fun c => (8662810625-1+2*2^10*c.k,115102741591838+c.lower,115103130681471+c.upper)) = pointBounds66062 := by
 decide +kernel
def cuts66063 : List PrefixCut := [⟨64,185884390,185884500⟩]
theorem checked66063 : checkPrefixCuts (2^48) 8662941697 10 Manual.Count131072.C066063.packed 64 cuts66063 = true := by
 decide +kernel
def cuts66064 : List PrefixCut := [⟨28,81585505,81585553⟩,
⟨64,184679425,184679529⟩]
theorem checked66064 : checkPrefixCuts (2^48) 8663072769 10 Manual.Count131072.C066064.packed 64 cuts66064 = true := by
 decide +kernel
def pointBounds66064 : List (Nat × Nat × Nat) := [(8663130112,115103198360609,115103587450513)]
theorem point_links_checked66064 : (cuts66064.take 1).map (fun c => (8663072769-1+2*2^10*c.k,115103116775104+c.lower,115103505864960+c.upper)) = pointBounds66064 := by
 decide +kernel
def cuts66065 : List PrefixCut := [⟨64,187828209,187828312⟩]
theorem checked66065 : checkPrefixCuts (2^48) 8663203841 10 Manual.Count131072.C066065.packed 64 cuts66065 = true := by
 decide +kernel
def cuts66066 : List PrefixCut := [⟨33,96236077,96236135⟩,
⟨64,186818172,186818281⟩]
theorem checked66066 : checkPrefixCuts (2^48) 8663334913 10 Manual.Count131072.C066066.packed 64 cuts66066 = true := by
 decide +kernel
def pointBounds66066 : List (Nat × Nat × Nat) := [(8663402496,115103585518815,115103974608936)]
theorem point_links_checked66066 : (cuts66066.take 1).map (fun c => (8663334913-1+2*2^10*c.k,115103489282738+c.lower,115103878372801+c.upper)) = pointBounds66066 := by
 decide +kernel
def cuts66067 : List PrefixCut := [⟨64,186847846,186847949⟩]
theorem checked66067 : checkPrefixCuts (2^48) 8663465985 10 Manual.Count131072.C066067.packed 64 cuts66067 = true := by
 decide +kernel
def cuts66068 : List PrefixCut := [⟨38,110430913,110430975⟩,
⟨64,186812523,186812631⟩]
theorem checked66068 : checkPrefixCuts (2^48) 8663597057 10 Manual.Count131072.C066068.packed 64 cuts66068 = true := by
 decide +kernel
def pointBounds66068 : List (Nat × Nat × Nat) := [(8663674880,115103973379669,115104362470006)]
theorem point_links_checked66068 : (cuts66068.take 1).map (fun c => (8663597057-1+2*2^10*c.k,115103862948756+c.lower,115104252039031+c.upper)) = pointBounds66068 := by
 decide +kernel
def cuts66069 : List PrefixCut := [⟨64,187589429,187589536⟩]
theorem checked66069 : checkPrefixCuts (2^48) 8663728129 10 Manual.Count131072.C066069.packed 64 cuts66069 = true := by
 decide +kernel
def cuts66070 : List PrefixCut := [⟨43,125437067,125437135⟩,
⟨64,187684049,187684150⟩]
theorem checked66070 : checkPrefixCuts (2^48) 8663859201 10 Manual.Count131072.C066070.packed 64 cuts66070 = true := by
 decide +kernel
def pointBounds66070 : List (Nat × Nat × Nat) := [(8663947264,115104362787775,115104751878333)]
theorem point_links_checked66070 : (cuts66070.take 1).map (fun c => (8663859201-1+2*2^10*c.k,115104237350708+c.lower,115104626441198+c.upper)) = pointBounds66070 := by
 decide +kernel
def cuts66071 : List PrefixCut := [⟨64,182580644,182580759⟩]
theorem checked66071 : checkPrefixCuts (2^48) 8663990273 10 Manual.Count131072.C066071.packed 64 cuts66071 = true := by
 decide +kernel
def cuts66072 : List PrefixCut := [⟨48,137193565,137193646⟩,
⟨64,183065187,183065296⟩]
theorem checked66072 : checkPrefixCuts (2^48) 8664121345 10 Manual.Count131072.C066072.packed 64 cuts66072 = true := by
 decide +kernel
def pointBounds66072 : List (Nat × Nat × Nat) := [(8664219648,115104744808966,115105133899753)]
theorem point_links_checked66072 : (cuts66072.take 1).map (fun c => (8664121345-1+2*2^10*c.k,115104607615401+c.lower,115104996706107+c.upper)) = pointBounds66072 := by
 decide +kernel
def cuts66073 : List PrefixCut := [⟨64,186570977,186571089⟩]
theorem checked66073 : checkPrefixCuts (2^48) 8664252417 10 Manual.Count131072.C066073.packed 64 cuts66073 = true := by
 decide +kernel
def cuts66074 : List PrefixCut := [⟨53,153172561,153172655⟩,
⟨64,185561086,185561199⟩]
theorem checked66074 : checkPrefixCuts (2^48) 8664383489 10 Manual.Count131072.C066074.packed 64 cuts66074 = true := by
 decide +kernel
def pointBounds66074 : List (Nat × Nat × Nat) := [(8664492032,115105130424126,115105519515147)]
theorem point_links_checked66074 : (cuts66074.take 1).map (fun c => (8664383489-1+2*2^10*c.k,115104977251565+c.lower,115105366342492+c.upper)) = pointBounds66074 := by
 decide +kernel
def cuts66075 : List PrefixCut := [⟨64,185265919,185266028⟩]
theorem checked66075 : checkPrefixCuts (2^48) 8664514561 10 Manual.Count131072.C066075.packed 64 cuts66075 = true := by
 decide +kernel
def cuts66076 : List PrefixCut := [⟨58,168923166,168923266⟩,
⟨64,186562510,186562621⟩]
theorem checked66076 : checkPrefixCuts (2^48) 8664645633 10 Manual.Count131072.C066076.packed 64 cuts66076 = true := by
 decide +kernel
def pointBounds66076 : List (Nat × Nat × Nat) := [(8664764416,115105517001736,115105906092985)]
theorem point_links_checked66076 : (cuts66076.take 1).map (fun c => (8664645633-1+2*2^10*c.k,115105348078570+c.lower,115105737169719+c.upper)) = pointBounds66076 := by
 decide +kernel
def cuts66077 : List PrefixCut := [⟨64,185195330,185195435⟩]
theorem checked66077 : checkPrefixCuts (2^48) 8664776705 10 Manual.Count131072.C066077.packed 64 cuts66077 = true := by
 decide +kernel
def cuts66078 : List PrefixCut := [⟨63,181814208,181814318⟩,
⟨64,184282990,184283102⟩]
theorem checked66078 : checkPrefixCuts (2^48) 8664907777 10 Manual.Count131072.C066078.packed 64 cuts66078 = true := by
 decide +kernel
def pointBounds66078 : List (Nat × Nat × Nat) := [(8665036800,115105901650618,115106290742093)]
theorem point_links_checked66078 : (cuts66078.take 1).map (fun c => (8664907777-1+2*2^10*c.k,115105719836410+c.lower,115106108927775+c.upper)) = pointBounds66078 := by
 decide +kernel
def cuts66079 : List PrefixCut := [⟨64,186716452,186716557⟩]
theorem checked66079 : checkPrefixCuts (2^48) 8665038849 10 Manual.Count131072.C066079.packed 64 cuts66079 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000189
