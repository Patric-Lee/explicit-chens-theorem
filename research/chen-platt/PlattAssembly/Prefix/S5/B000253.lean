import PlattAssemblyKernel
import PlattCertificates.Count131072.C048096
import PlattCertificates.Count131072.C048097
import PlattCertificates.Count131072.C048098
import PlattCertificates.Count131072.C048099
import PlattCertificates.Count131072.C048100
import PlattCertificates.Count131072.C048101
import PlattCertificates.Count131072.C048102
import PlattCertificates.Count131072.C048103
import PlattCertificates.Count131072.C048104
import PlattCertificates.Count131072.C048105
import PlattCertificates.Count131072.C048106
import PlattCertificates.Count131072.C048107
import PlattCertificates.Count131072.C048108
import PlattCertificates.Count131072.C048109
import PlattCertificates.Count131072.C048110
import PlattCertificates.Count131072.C048111
import PlattCertificates.Count131072.C048112
import PlattCertificates.Count131072.C048113
import PlattCertificates.Count131072.C048114
import PlattCertificates.Count131072.C048115
import PlattCertificates.Count131072.C048116
import PlattCertificates.Count131072.C048117
import PlattCertificates.Count131072.C048118
import PlattCertificates.Count131072.C048119
import PlattCertificates.Count131072.C048120
import PlattCertificates.Count131072.C048121
import PlattCertificates.Count131072.C048122
import PlattCertificates.Count131072.C048123
import PlattCertificates.Count131072.C048124
import PlattCertificates.Count131072.C048125
import PlattCertificates.Count131072.C048126
import PlattCertificates.Count131072.C048127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000253
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48096 : List PrefixCut := [⟨64,260010249,260010401⟩]
theorem checked48096 : checkPrefixCuts (2^48) 6307971073 10 Manual.Count131072.C048096.packed 64 cuts48096 = true := by
 decide +kernel
def cuts48097 : List PrefixCut := [⟨3,12136952,12136959⟩,
⟨64,258130775,258130928⟩]
theorem checked48097 : checkPrefixCuts (2^48) 6308102145 10 Manual.Count131072.C048097.packed 64 cuts48097 = true := by
 decide +kernel
def pointBounds48097 : List (Nat × Nat × Nat) := [(6308108288,111173609569611,111173996415908)]
theorem point_links_checked48097 : (cuts48097.take 1).map (fun c => (6308102145-1+2*2^10*c.k,111173597432659+c.lower,111173984278949+c.upper)) = pointBounds48097 := by
 decide +kernel
def cuts48098 : List PrefixCut := [⟨36,145773487,145773572⟩,
⟨64,257991574,257991723⟩]
theorem checked48098 : checkPrefixCuts (2^48) 6308233217 10 Manual.Count131072.C048098.packed 64 cuts48098 = true := by
 decide +kernel
def pointBounds48098 : List (Nat × Nat × Nat) := [(6308306944,111174001336921,111174388183449)]
theorem point_links_checked48098 : (cuts48098.take 1).map (fun c => (6308233217-1+2*2^10*c.k,111173855563434+c.lower,111174242409877+c.upper)) = pointBounds48098 := by
 decide +kernel
def cuts48099 : List PrefixCut := [⟨64,257004570,257004723⟩]
theorem checked48099 : checkPrefixCuts (2^48) 6308364289 10 Manual.Count131072.C048099.packed 64 cuts48099 = true := by
 decide +kernel
def cuts48100 : List PrefixCut := [⟨5,20479822,20479837⟩,
⟨64,259676310,259676456⟩]
theorem checked48100 : checkPrefixCuts (2^48) 6308495361 10 Manual.Count131072.C048100.packed 64 cuts48100 = true := by
 decide +kernel
def pointBounds48100 : List (Nat × Nat × Nat) := [(6308505600,111174391039400,111174777886160)]
theorem point_links_checked48100 : (cuts48100.take 1).map (fun c => (6308495361-1+2*2^10*c.k,111174370559578+c.lower,111174757406323+c.upper)) = pointBounds48100 := by
 decide +kernel
def cuts48101 : List PrefixCut := [⟨38,154464696,154464781⟩,
⟨64,259046292,259046436⟩]
theorem checked48101 : checkPrefixCuts (2^48) 6308626433 10 Manual.Count131072.C048101.packed 64 cuts48101 = true := by
 decide +kernel
def pointBounds48101 : List (Nat × Nat × Nat) := [(6308704256,111174784700584,111175171547560)]
theorem point_links_checked48101 : (cuts48101.take 1).map (fun c => (6308626433-1+2*2^10*c.k,111174630235888+c.lower,111175017082779+c.upper)) = pointBounds48101 := by
 decide +kernel
def cuts48102 : List PrefixCut := [⟨64,259665522,259665669⟩]
theorem checked48102 : checkPrefixCuts (2^48) 6308757505 10 Manual.Count131072.C048102.packed 64 cuts48102 = true := by
 decide +kernel
def cuts48103 : List PrefixCut := [⟨7,28643187,28643205⟩,
⟨64,258678621,258678767⟩]
theorem checked48103 : checkPrefixCuts (2^48) 6308888577 10 Manual.Count131072.C048103.packed 64 cuts48103 = true := by
 decide +kernel
def pointBounds48103 : List (Nat × Nat × Nat) := [(6308902912,111175177590889,111175564438089)]
theorem point_links_checked48103 : (cuts48103.take 1).map (fun c => (6308888577-1+2*2^10*c.k,111175148947702+c.lower,111175535794884+c.upper)) = pointBounds48103 := by
 decide +kernel
def cuts48104 : List PrefixCut := [⟨40,159094929,159095023⟩,
⟨64,257914781,257914932⟩]
theorem checked48104 : checkPrefixCuts (2^48) 6309019649 10 Manual.Count131072.C048104.packed 64 cuts48104 = true := by
 decide +kernel
def pointBounds48104 : List (Nat × Nat × Nat) := [(6309101568,111175566721252,111175953568674)]
theorem point_links_checked48104 : (cuts48104.take 1).map (fun c => (6309019649-1+2*2^10*c.k,111175407626323+c.lower,111175794473651+c.upper)) = pointBounds48104 := by
 decide +kernel
def cuts48105 : List PrefixCut := [⟨64,258712493,258712635⟩]
theorem checked48105 : checkPrefixCuts (2^48) 6309150721 10 Manual.Count131072.C048105.packed 64 cuts48105 = true := by
 decide +kernel
def cuts48106 : List PrefixCut := [⟨9,36805528,36805550⟩,
⟨64,259153220,259153373⟩]
theorem checked48106 : checkPrefixCuts (2^48) 6309281793 10 Manual.Count131072.C048106.packed 64 cuts48106 = true := by
 decide +kernel
def pointBounds48106 : List (Nat × Nat × Nat) := [(6309300224,111175961059125,111176347906768)]
theorem point_links_checked48106 : (cuts48106.take 1).map (fun c => (6309281793-1+2*2^10*c.k,111175924253597+c.lower,111176311101218+c.upper)) = pointBounds48106 := by
 decide +kernel
def cuts48107 : List PrefixCut := [⟨42,168854884,168854977⟩,
⟨64,259370873,259371015⟩]
theorem checked48107 : checkPrefixCuts (2^48) 6309412865 10 Manual.Count131072.C048107.packed 64 cuts48107 = true := by
 decide +kernel
def pointBounds48107 : List (Nat × Nat × Nat) := [(6309498880,111176352261701,111176739109568)]
theorem point_links_checked48107 : (cuts48107.take 1).map (fun c => (6309412865-1+2*2^10*c.k,111176183406817+c.lower,111176570254591+c.upper)) = pointBounds48107 := by
 decide +kernel
def cuts48108 : List PrefixCut := [⟨64,259499339,259499491⟩]
theorem checked48108 : checkPrefixCuts (2^48) 6309543937 10 Manual.Count131072.C048108.packed 64 cuts48108 = true := by
 decide +kernel
def cuts48109 : List PrefixCut := [⟨11,44966848,44966872⟩,
⟨64,258244898,258245043⟩]
theorem checked48109 : checkPrefixCuts (2^48) 6309675009 10 Manual.Count131072.C048109.packed 64 cuts48109 = true := by
 decide +kernel
def pointBounds48109 : List (Nat × Nat × Nat) := [(6309697536,111176747243877,111177134091969)]
theorem point_links_checked48109 : (cuts48109.take 1).map (fun c => (6309675009-1+2*2^10*c.k,111176702277029+c.lower,111177089125097+c.upper)) = pointBounds48109 := by
 decide +kernel
def cuts48110 : List PrefixCut := [⟨44,181245567,181245670⟩,
⟨64,262834219,262834366⟩]
theorem checked48110 : checkPrefixCuts (2^48) 6309806081 10 Manual.Count131072.C048110.packed 64 cuts48110 = true := by
 decide +kernel
def pointBounds48110 : List (Nat × Nat × Nat) := [(6309896192,111177141767494,111177528615810)]
theorem point_links_checked48110 : (cuts48110.take 1).map (fun c => (6309806081-1+2*2^10*c.k,111176960521927+c.lower,111177347370140+c.upper)) = pointBounds48110 := by
 decide +kernel
def cuts48111 : List PrefixCut := [⟨64,257163564,257163716⟩]
theorem checked48111 : checkPrefixCuts (2^48) 6309937153 10 Manual.Count131072.C048111.packed 64 cuts48111 = true := by
 decide +kernel
def cuts48112 : List PrefixCut := [⟨13,53216354,53216387⟩,
⟨64,260057656,260057802⟩]
theorem checked48112 : checkPrefixCuts (2^48) 6310068225 10 Manual.Count131072.C048112.packed 64 cuts48112 = true := by
 decide +kernel
def pointBounds48112 : List (Nat × Nat × Nat) := [(6310094848,111177533736064,111177920584609)]
theorem point_links_checked48112 : (cuts48112.take 1).map (fun c => (6310068225-1+2*2^10*c.k,111177480519710+c.lower,111177867368222+c.upper)) = pointBounds48112 := by
 decide +kernel
def cuts48113 : List PrefixCut := [⟨46,188415787,188415894⟩,
⟨64,261658087,261658236⟩]
theorem checked48113 : checkPrefixCuts (2^48) 6310199297 10 Manual.Count131072.C048113.packed 64 cuts48113 = true := by
 decide +kernel
def pointBounds48113 : List (Nat × Nat × Nat) := [(6310293504,111177928993153,111178315841918)]
theorem point_links_checked48113 : (cuts48113.take 1).map (fun c => (6310199297-1+2*2^10*c.k,111177740577366+c.lower,111178127426024+c.upper)) = pointBounds48113 := by
 decide +kernel
def cuts48114 : List PrefixCut := [⟨64,260091475,260091622⟩]
theorem checked48114 : checkPrefixCuts (2^48) 6310330369 10 Manual.Count131072.C048114.packed 64 cuts48114 = true := by
 decide +kernel
def cuts48115 : List PrefixCut := [⟨15,60260516,60260551⟩,
⟨64,258391104,258391251⟩]
theorem checked48115 : checkPrefixCuts (2^48) 6310461441 10 Manual.Count131072.C048115.packed 64 cuts48115 = true := by
 decide +kernel
def pointBounds48115 : List (Nat × Nat × Nat) := [(6310492160,111178322587444,111178709436433)]
theorem point_links_checked48115 : (cuts48115.take 1).map (fun c => (6310461441-1+2*2^10*c.k,111178262326928+c.lower,111178649175882+c.upper)) = pointBounds48115 := by
 decide +kernel
def cuts48116 : List PrefixCut := [⟨48,191838418,191838533⟩,
⟨64,256557008,256557160⟩]
theorem checked48116 : checkPrefixCuts (2^48) 6310592513 10 Manual.Count131072.C048116.packed 64 cuts48116 = true := by
 decide +kernel
def pointBounds48116 : List (Nat × Nat × Nat) := [(6310690816,111178712556450,111179099405666)]
theorem point_links_checked48116 : (cuts48116.take 1).map (fun c => (6310592513-1+2*2^10*c.k,111178520718032+c.lower,111178907567133+c.upper)) = pointBounds48116 := by
 decide +kernel
def cuts48117 : List PrefixCut := [⟨64,259406239,259406382⟩]
theorem checked48117 : checkPrefixCuts (2^48) 6310723585 10 Manual.Count131072.C048117.packed 64 cuts48117 = true := by
 decide +kernel
def cuts48118 : List PrefixCut := [⟨17,67928209,67928245⟩,
⟨64,257705969,257706114⟩]
theorem checked48118 : checkPrefixCuts (2^48) 6310854657 10 Manual.Count131072.C048118.packed 64 cuts48118 = true := by
 decide +kernel
def pointBounds48118 : List (Nat × Nat × Nat) := [(6310889472,111179104609488,111179491458920)]
theorem point_links_checked48118 : (cuts48118.take 1).map (fun c => (6310854657-1+2*2^10*c.k,111179036681279+c.lower,111179423530675+c.upper)) = pointBounds48118 := by
 decide +kernel
def cuts48119 : List PrefixCut := [⟨50,199765288,199765401⟩,
⟨64,256942436,256942579⟩]
theorem checked48119 : checkPrefixCuts (2^48) 6310985729 10 Manual.Count131072.C048119.packed 64 cuts48119 = true := by
 decide +kernel
def pointBounds48119 : List (Nat × Nat × Nat) := [(6311088128,111179494152536,111179881002190)]
theorem point_links_checked48119 : (cuts48119.take 1).map (fun c => (6310985729-1+2*2^10*c.k,111179294387248+c.lower,111179681236789+c.upper)) = pointBounds48119 := by
 decide +kernel
def cuts48120 : List PrefixCut := [⟨64,260326637,260326786⟩]
theorem checked48120 : checkPrefixCuts (2^48) 6311116801 10 Manual.Count131072.C048120.packed 64 cuts48120 = true := by
 decide +kernel
def cuts48121 : List PrefixCut := [⟨19,79787239,79787287⟩,
⟨64,261748410,261748563⟩]
theorem checked48121 : checkPrefixCuts (2^48) 6311247873 10 Manual.Count131072.C048121.packed 64 cuts48121 = true := by
 decide +kernel
def pointBounds48121 : List (Nat × Nat × Nat) := [(6311286784,111179891443560,111180278293441)]
theorem point_links_checked48121 : (cuts48121.take 1).map (fun c => (6311247873-1+2*2^10*c.k,111179811656321+c.lower,111180198506154+c.upper)) = pointBounds48121 := by
 decide +kernel
def cuts48122 : List PrefixCut := [⟨52,209296665,209296784⟩,
⟨64,256837241,256837389⟩]
theorem checked48122 : checkPrefixCuts (2^48) 6311378945 10 Manual.Count131072.C048122.packed 64 cuts48122 = true := by
 decide +kernel
def pointBounds48122 : List (Nat × Nat × Nat) := [(6311485440,111180282701396,111180669551501)]
theorem point_links_checked48122 : (cuts48122.take 1).map (fun c => (6311378945-1+2*2^10*c.k,111180073404731+c.lower,111180460254717+c.upper)) = pointBounds48122 := by
 decide +kernel
def cuts48123 : List PrefixCut := [⟨64,258571159,258571310⟩]
theorem checked48123 : checkPrefixCuts (2^48) 6311510017 10 Manual.Count131072.C048123.packed 64 cuts48123 = true := by
 decide +kernel
def cuts48124 : List PrefixCut := [⟨21,86828410,86828458⟩,
⟨64,261687499,261687652⟩]
theorem checked48124 : checkPrefixCuts (2^48) 6311641089 10 Manual.Count131072.C048124.packed 64 cuts48124 = true := by
 decide +kernel
def pointBounds48124 : List (Nat × Nat × Nat) := [(6311684096,111180675641541,111181062491874)]
theorem point_links_checked48124 : (cuts48124.take 1).map (fun c => (6311641089-1+2*2^10*c.k,111180588813131+c.lower,111180975663416+c.upper)) = pointBounds48124 := by
 decide +kernel
def cuts48125 : List PrefixCut := [⟨54,217578172,217578297⟩,
⟨64,259140124,259140275⟩]
theorem checked48125 : checkPrefixCuts (2^48) 6311772161 10 Manual.Count131072.C048125.packed 64 cuts48125 = true := by
 decide +kernel
def pointBounds48125 : List (Nat × Nat × Nat) := [(6311882752,111181068078802,111181454929365)]
theorem point_links_checked48125 : (cuts48125.take 1).map (fun c => (6311772161-1+2*2^10*c.k,111180850500630+c.lower,111181237351068+c.upper)) = pointBounds48125 := by
 decide +kernel
def cuts48126 : List PrefixCut := [⟨64,261854982,261855131⟩]
theorem checked48126 : checkPrefixCuts (2^48) 6311903233 10 Manual.Count131072.C048126.packed 64 cuts48126 = true := by
 decide +kernel
def cuts48127 : List PrefixCut := [⟨23,91683629,91683683⟩,
⟨64,258415899,258416049⟩]
theorem checked48127 : checkPrefixCuts (2^48) 6312034305 10 Manual.Count131072.C048127.packed 64 cuts48127 = true := by
 decide +kernel
def pointBounds48127 : List (Nat × Nat × Nat) := [(6312081408,111181463179365,111181850030157)]
theorem point_links_checked48127 : (cuts48127.take 1).map (fun c => (6312034305-1+2*2^10*c.k,111181371495736+c.lower,111181758346474+c.upper)) = pointBounds48127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000253
