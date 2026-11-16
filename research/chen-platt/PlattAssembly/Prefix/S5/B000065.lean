import PlattAssemblyKernel
import PlattCertificates.Count131072.C042080
import PlattCertificates.Count131072.C042081
import PlattCertificates.Count131072.C042082
import PlattCertificates.Count131072.C042083
import PlattCertificates.Count131072.C042084
import PlattCertificates.Count131072.C042085
import PlattCertificates.Count131072.C042086
import PlattCertificates.Count131072.C042087
import PlattCertificates.Count131072.C042088
import PlattCertificates.Count131072.C042089
import PlattCertificates.Count131072.C042090
import PlattCertificates.Count131072.C042091
import PlattCertificates.Count131072.C042092
import PlattCertificates.Count131072.C042093
import PlattCertificates.Count131072.C042094
import PlattCertificates.Count131072.C042095
import PlattCertificates.Count131072.C042096
import PlattCertificates.Count131072.C042097
import PlattCertificates.Count131072.C042098
import PlattCertificates.Count131072.C042099
import PlattCertificates.Count131072.C042100
import PlattCertificates.Count131072.C042101
import PlattCertificates.Count131072.C042102
import PlattCertificates.Count131072.C042103
import PlattCertificates.Count131072.C042104
import PlattCertificates.Count131072.C042105
import PlattCertificates.Count131072.C042106
import PlattCertificates.Count131072.C042107
import PlattCertificates.Count131072.C042108
import PlattCertificates.Count131072.C042109
import PlattCertificates.Count131072.C042110
import PlattCertificates.Count131072.C042111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42080 : List PrefixCut := [⟨32,148859313,148859400⟩,
⟨64,299399731,299399906⟩]
theorem checked42080 : checkPrefixCuts (2^48) 5519441921 10 Manual.Count131072.C042080.packed 64 cuts42080 = true := by
 decide +kernel
def pointBounds42080 : List (Nat × Nat × Nat) := [(5519507456,109502694947559,109503080828700)]
theorem point_links_checked42080 : (cuts42080.take 1).map (fun c => (5519441921-1+2*2^10*c.k,109502546088246+c.lower,109502931969300+c.upper)) = pointBounds42080 := by
 decide +kernel
def cuts42081 : List PrefixCut := [⟨53,247327041,247327179⟩,
⟨64,298525686,298525854⟩]
theorem checked42081 : checkPrefixCuts (2^48) 5519572993 10 Manual.Count131072.C042081.packed 64 cuts42081 = true := by
 decide +kernel
def pointBounds42081 : List (Nat × Nat × Nat) := [(5519681536,109503092815018,109503478696385)]
theorem point_links_checked42081 : (cuts42081.take 1).map (fun c => (5519572993-1+2*2^10*c.k,109502845487977+c.lower,109503231369206+c.upper)) = pointBounds42081 := by
 decide +kernel
def cuts42082 : List PrefixCut := [⟨64,296019931,296020101⟩]
theorem checked42082 : checkPrefixCuts (2^48) 5519704065 10 Manual.Count131072.C042082.packed 64 cuts42082 = true := by
 decide +kernel
def cuts42083 : List PrefixCut := [⟨10,46811810,46811836⟩,
⟨64,295910895,295911066⟩]
theorem checked42083 : checkPrefixCuts (2^48) 5519835137 10 Manual.Count131072.C042083.packed 64 cuts42083 = true := by
 decide +kernel
def pointBounds42083 : List (Nat × Nat × Nat) := [(5519855616,109503486845404,109503872726997)]
theorem point_links_checked42083 : (cuts42083.take 1).map (fun c => (5519835137-1+2*2^10*c.k,109503440033594+c.lower,109503825915161+c.upper)) = pointBounds42083 := by
 decide +kernel
def cuts42084 : List PrefixCut := [⟨31,141961305,141961387⟩,
⟨64,294935027,294935200⟩]
theorem checked42084 : checkPrefixCuts (2^48) 5519966209 10 Manual.Count131072.C042084.packed 64 cuts42084 = true := by
 decide +kernel
def pointBounds42084 : List (Nat × Nat × Nat) := [(5520029696,109503877905794,109504263787614)]
theorem point_links_checked42084 : (cuts42084.take 1).map (fun c => (5519966209-1+2*2^10*c.k,109503735944489+c.lower,109504121826227+c.upper)) = pointBounds42084 := by
 decide +kernel
def cuts42085 : List PrefixCut := [⟨52,241745668,241745810⟩,
⟨64,299670116,299670292⟩]
theorem checked42085 : checkPrefixCuts (2^48) 5520097281 10 Manual.Count131072.C042085.packed 64 cuts42085 = true := by
 decide +kernel
def pointBounds42085 : List (Nat × Nat × Nat) := [(5520203776,109504272625184,109504658507237)]
theorem point_links_checked42085 : (cuts42085.take 1).map (fun c => (5520097281-1+2*2^10*c.k,109504030879516+c.lower,109504416761427+c.upper)) = pointBounds42085 := by
 decide +kernel
def cuts42086 : List PrefixCut := [⟨64,298286304,298286478⟩]
theorem checked42086 : checkPrefixCuts (2^48) 5520228353 10 Manual.Count131072.C042086.packed 64 cuts42086 = true := by
 decide +kernel
def cuts42087 : List PrefixCut := [⟨9,42218415,42218439⟩,
⟨64,302307278,302307457⟩]
theorem checked42087 : checkPrefixCuts (2^48) 5520359425 10 Manual.Count131072.C042087.packed 64 cuts42087 = true := by
 decide +kernel
def pointBounds42087 : List (Nat × Nat × Nat) := [(5520377856,109504671054351,109505056936636)]
theorem point_links_checked42087 : (cuts42087.take 1).map (fun c => (5520359425-1+2*2^10*c.k,109504628835936+c.lower,109505014718197+c.upper)) = pointBounds42087 := by
 decide +kernel
def cuts42088 : List PrefixCut := [⟨30,141998832,141998915⟩,
⟨64,299291903,299292079⟩]
theorem checked42088 : checkPrefixCuts (2^48) 5520490497 10 Manual.Count131072.C042088.packed 64 cuts42088 = true := by
 decide +kernel
def pointBounds42088 : List (Nat × Nat × Nat) := [(5520551936,109505073142046,109505459024569)]
theorem point_links_checked42088 : (cuts42088.take 1).map (fun c => (5520490497-1+2*2^10*c.k,109504931143214+c.lower,109505317025654+c.upper)) = pointBounds42088 := by
 decide +kernel
def cuts42089 : List PrefixCut := [⟨51,239428422,239428566⟩,
⟨64,298469053,298469233⟩]
theorem checked42089 : checkPrefixCuts (2^48) 5520621569 10 Manual.Count131072.C042089.packed 64 cuts42089 = true := by
 decide +kernel
def pointBounds42089 : List (Nat × Nat × Nat) := [(5520726016,109505469863539,109505855746299)]
theorem point_links_checked42089 : (cuts42089.take 1).map (fun c => (5520621569-1+2*2^10*c.k,109505230435117+c.lower,109505616317733+c.upper)) = pointBounds42089 := by
 decide +kernel
def cuts42090 : List PrefixCut := [⟨64,299430602,299430775⟩]
theorem checked42090 : checkPrefixCuts (2^48) 5520752641 10 Manual.Count131072.C042090.packed 64 cuts42090 = true := by
 decide +kernel
def cuts42091 : List PrefixCut := [⟨8,37778841,37778863⟩,
⟨64,294988016,294988188⟩]
theorem checked42091 : checkPrefixCuts (2^48) 5520883713 10 Manual.Count131072.C042091.packed 64 cuts42091 = true := by
 decide +kernel
def pointBounds42091 : List (Nat × Nat × Nat) := [(5520900096,109505866113613,109506251996604)]
theorem point_links_checked42091 : (cuts42091.take 1).map (fun c => (5520883713-1+2*2^10*c.k,109505828334772+c.lower,109506214217741+c.upper)) = pointBounds42091 := by
 decide +kernel
def cuts42092 : List PrefixCut := [⟨29,133675283,133675360⟩,
⟨64,294471183,294471351⟩]
theorem checked42092 : checkPrefixCuts (2^48) 5521014785 10 Manual.Count131072.C042092.packed 64 cuts42092 = true := by
 decide +kernel
def pointBounds42092 : List (Nat × Nat × Nat) := [(5521074176,109506256998071,109506642881289)]
theorem point_links_checked42092 : (cuts42092.take 1).map (fun c => (5521014785-1+2*2^10*c.k,109506123322788+c.lower,109506509205929+c.upper)) = pointBounds42092 := by
 decide +kernel
def cuts42093 : List PrefixCut := [⟨50,233899756,233899895⟩,
⟨64,296911243,296911419⟩]
theorem checked42093 : checkPrefixCuts (2^48) 5521145857 10 Manual.Count131072.C042093.packed 64 cuts42093 = true := by
 decide +kernel
def pointBounds42093 : List (Nat × Nat × Nat) := [(5521248256,109506651693727,109507037577175)]
theorem point_links_checked42093 : (cuts42093.take 1).map (fun c => (5521145857-1+2*2^10*c.k,109506417793971+c.lower,109506803677280+c.upper)) = pointBounds42093 := by
 decide +kernel
def cuts42094 : List PrefixCut := [⟨64,298535541,298535715⟩]
theorem checked42094 : checkPrefixCuts (2^48) 5521276929 10 Manual.Count131072.C042094.packed 64 cuts42094 = true := by
 decide +kernel
def cuts42095 : List PrefixCut := [⟨7,32167599,32167617⟩,
⟨64,297610836,297611013⟩]
theorem checked42095 : checkPrefixCuts (2^48) 5521408001 10 Manual.Count131072.C042095.packed 64 cuts42095 = true := by
 decide +kernel
def pointBounds42095 : List (Nat × Nat × Nat) := [(5521422336,109507045408354,109507431292031)]
theorem point_links_checked42095 : (cuts42095.take 1).map (fun c => (5521408001-1+2*2^10*c.k,109507013240755+c.lower,109507399124414+c.upper)) = pointBounds42095 := by
 decide +kernel
def cuts42096 : List PrefixCut := [⟨28,131572541,131572617⟩,
⟨64,299693842,299694022⟩]
theorem checked42096 : checkPrefixCuts (2^48) 5521539073 10 Manual.Count131072.C042096.packed 64 cuts42096 = true := by
 decide +kernel
def pointBounds42096 : List (Nat × Nat × Nat) := [(5521596416,109507442424132,109507828308044)]
theorem point_links_checked42096 : (cuts42096.take 1).map (fun c => (5521539073-1+2*2^10*c.k,109507310851591+c.lower,109507696735427+c.upper)) = pointBounds42096 := by
 decide +kernel
def cuts42097 : List PrefixCut := [⟨49,227199774,227199904⟩,
⟨64,299431826,299431997⟩]
theorem checked42097 : checkPrefixCuts (2^48) 5521670145 10 Manual.Count131072.C042097.packed 64 cuts42097 = true := by
 decide +kernel
def pointBounds42097 : List (Nat × Nat × Nat) := [(5521770496,109507837745207,109508223629353)]
theorem point_links_checked42097 : (cuts42097.take 1).map (fun c => (5521670145-1+2*2^10*c.k,109507610545433+c.lower,109507996429449+c.upper)) = pointBounds42097 := by
 decide +kernel
def cuts42098 : List PrefixCut := [⟨64,296926982,296927158⟩]
theorem checked42098 : checkPrefixCuts (2^48) 5521801217 10 Manual.Count131072.C042098.packed 64 cuts42098 = true := by
 decide +kernel
def cuts42099 : List PrefixCut := [⟨6,27576895,27576913⟩,
⟨64,298041333,298041507⟩]
theorem checked42099 : checkPrefixCuts (2^48) 5521932289 10 Manual.Count131072.C042099.packed 64 cuts42099 = true := by
 decide +kernel
def pointBounds42099 : List (Nat × Nat × Nat) := [(5521944576,109508234481136,109508620365517)]
theorem point_links_checked42099 : (cuts42099.take 1).map (fun c => (5521932289-1+2*2^10*c.k,109508206904241+c.lower,109508592788604+c.upper)) = pointBounds42099 := by
 decide +kernel
def cuts42100 : List PrefixCut := [⟨27,126513792,126513868⟩,
⟨64,300328013,300328187⟩]
theorem checked42100 : checkPrefixCuts (2^48) 5522063361 10 Manual.Count131072.C042100.packed 64 cuts42100 = true := by
 decide +kernel
def pointBounds42100 : List (Nat × Nat × Nat) := [(5522118656,109508631459366,109509017343979)]
theorem point_links_checked42100 : (cuts42100.take 1).map (fun c => (5522063361-1+2*2^10*c.k,109508504945574+c.lower,109508890830111+c.upper)) = pointBounds42100 := by
 decide +kernel
def cuts42101 : List PrefixCut := [⟨48,227382136,227382269⟩,
⟨64,302767518,302767693⟩]
theorem checked42101 : checkPrefixCuts (2^48) 5522194433 10 Manual.Count131072.C042101.packed 64 cuts42101 = true := by
 decide +kernel
def pointBounds42101 : List (Nat × Nat × Nat) := [(5522292736,109509032655723,109509418540567)]
theorem point_links_checked42101 : (cuts42101.take 1).map (fun c => (5522194433-1+2*2^10*c.k,109508805273587+c.lower,109509191158298+c.upper)) = pointBounds42101 := by
 decide +kernel
def cuts42102 : List PrefixCut := [⟨64,299447270,299447453⟩]
theorem checked42102 : checkPrefixCuts (2^48) 5522325505 10 Manual.Count131072.C042102.packed 64 cuts42102 = true := by
 decide +kernel
def cuts42103 : List PrefixCut := [⟨5,23139970,23139985⟩,
⟨64,298777577,298777751⟩]
theorem checked42103 : checkPrefixCuts (2^48) 5522456577 10 Manual.Count131072.C042103.packed 64 cuts42103 = true := by
 decide +kernel
def pointBounds42103 : List (Nat × Nat × Nat) := [(5522466816,109509430628345,109509816513429)]
theorem point_links_checked42103 : (cuts42103.take 1).map (fun c => (5522456577-1+2*2^10*c.k,109509407488375+c.lower,109509793373444+c.upper)) = pointBounds42103 := by
 decide +kernel
def cuts42104 : List PrefixCut := [⟨26,122016657,122016728⟩,
⟨64,296069233,296069405⟩]
theorem checked42104 : checkPrefixCuts (2^48) 5522587649 10 Manual.Count131072.C042104.packed 64 cuts42104 = true := by
 decide +kernel
def pointBounds42104 : List (Nat × Nat × Nat) := [(5522640896,109509828282609,109510214167923)]
theorem point_links_checked42104 : (cuts42104.take 1).map (fun c => (5522587649-1+2*2^10*c.k,109509706265952+c.lower,109510092151195+c.upper)) = pointBounds42104 := by
 decide +kernel
def cuts42105 : List PrefixCut := [⟨47,214364163,214364289⟩,
⟨64,294431242,294431415⟩]
theorem checked42105 : checkPrefixCuts (2^48) 5522718721 10 Manual.Count131072.C042105.packed 64 cuts42105 = true := by
 decide +kernel
def pointBounds42105 : List (Nat × Nat × Nat) := [(5522814976,109510216699348,109510602584889)]
theorem point_links_checked42105 : (cuts42105.take 1).map (fun c => (5522718721-1+2*2^10*c.k,109510002335185+c.lower,109510388220600+c.upper)) = pointBounds42105 := by
 decide +kernel
def cuts42106 : List PrefixCut := [⟨64,297482165,297482337⟩]
theorem checked42106 : checkPrefixCuts (2^48) 5522849793 10 Manual.Count131072.C042106.packed 64 cuts42106 = true := by
 decide +kernel
def cuts42107 : List PrefixCut := [⟨4,19519316,19519327⟩,
⟨64,298545409,298545583⟩]
theorem checked42107 : checkPrefixCuts (2^48) 5522980865 10 Manual.Count131072.C042107.packed 64 cuts42107 = true := by
 decide +kernel
def pointBounds42107 : List (Nat × Nat × Nat) := [(5522989056,109510613767908,109510999653679)]
theorem point_links_checked42107 : (cuts42107.take 1).map (fun c => (5522980865-1+2*2^10*c.k,109510594248592+c.lower,109510980134352+c.upper)) = pointBounds42107 := by
 decide +kernel
def cuts42108 : List PrefixCut := [⟨25,115176076,115176139⟩,
⟨64,293900710,293900874⟩]
theorem checked42108 : checkPrefixCuts (2^48) 5523111937 10 Manual.Count131072.C042108.packed 64 cuts42108 = true := by
 decide +kernel
def pointBounds42108 : List (Nat × Nat × Nat) := [(5523163136,109511007970077,109511393856074)]
theorem point_links_checked42108 : (cuts42108.take 1).map (fun c => (5523111937-1+2*2^10*c.k,109510892794001+c.lower,109511278679935+c.upper)) = pointBounds42108 := by
 decide +kernel
def cuts42109 : List PrefixCut := [⟨46,214853493,214853619⟩,
⟨64,298276409,298276583⟩]
theorem checked42109 : checkPrefixCuts (2^48) 5523243009 10 Manual.Count131072.C042109.packed 64 cuts42109 = true := by
 decide +kernel
def pointBounds42109 : List (Nat × Nat × Nat) := [(5523337216,109511401548204,109511787434428)]
theorem point_links_checked42109 : (cuts42109.take 1).map (fun c => (5523243009-1+2*2^10*c.k,109511186694711+c.lower,109511572580809+c.upper)) = pointBounds42109 := by
 decide +kernel
def cuts42110 : List PrefixCut := [⟨64,297963585,297963757⟩]
theorem checked42110 : checkPrefixCuts (2^48) 5523374081 10 Manual.Count131072.C042110.packed 64 cuts42110 = true := by
 decide +kernel
def cuts42111 : List PrefixCut := [⟨3,14064806,14064814⟩,
⟨64,297141147,297141321⟩]
theorem checked42111 : checkPrefixCuts (2^48) 5523505153 10 Manual.Count131072.C042111.packed 64 cuts42111 = true := by
 decide +kernel
def pointBounds42111 : List (Nat × Nat × Nat) := [(5523511296,109511796999511,109512182885963)]
theorem point_links_checked42111 : (cuts42111.take 1).map (fun c => (5523505153-1+2*2^10*c.k,109511782934705+c.lower,109512168821149+c.upper)) = pointBounds42111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000065
